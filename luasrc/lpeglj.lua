--[[
** LPeg Parser in LuaJIT
** based on LPeg - PEG pattern matching for Lua
** Lua.org & PUC-Rio  written by Roberto Ierusalimschy
**
** Copyright (C) 2012 Rostislav Sacek. All rights reserved.
**
** Permission is hereby granted, free of charge, to any person obtaining
** a copy of this software and associated documentation files (the
** "Software"), to deal in the Software without restriction, including
** without limitation the rights to use, copy, modify, merge, publish,
** distribute, sublicense, and/or sell copies of the Software, and to
** permit persons to whom the Software is furnished to do so, subject to
** the following conditions:
**
** The above copyright notice and this permission notice shall be
** included in all copies or substantial portions of the Software.
**
** THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
** EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
** MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
** IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
** CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
** TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
** SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**
** [ MIT license: http://www.opensource.org/licenses/mit-license.php ]
--]]

local ffi = require'ffi'
local lpeg = require"lpeg"

ffi.cdef[[
typedef unsigned char byte;
typedef const char *(*PattFunc) (const char *s,  /* current position */
                                 const char *e,  /* string end */
                                 const char *o,  /* string start */
                                 const void *ud);  /* user data
]]

ffi.cdef[[
typedef union _Instruction {
  struct Inst {
    byte code;
    byte aux;
    short offset;
  };
  PattFunc f;
  int iv;
  byte buff[1];
} Instruction;
]]

ffi.cdef[[
typedef enum Opcode {
  IAny, IChar, ISet, ISpan,
  IBack,
  IRet, IEnd,
  IChoice, IJmp, ICall, IOpenCall,
  ICommit, IPartialCommit, IBackCommit, IFailTwice, IFail, IGiveup,
  IFunc,
  IFullCapture, IEmptyCapture, IEmptyCaptureIdx,
  IOpenCapture, ICloseCapture, ICloseRunTime
} Opcode;
]]

ffi.cdef[[
static const int UCHAR_MAX = 255;
static const int CHAR_BIT = 8;
static const int CHARSETSIZE = (UCHAR_MAX / CHAR_BIT) + 1;
static const int INITCAPSIZE =	32;
static const int MAXSTRCAPS	= 10;
static const int INITBACK =	100;
/* default maximum size for call/backtrack stack */
static const int MAXBACK = INITBACK;
]]

ffi.cdef[[
typedef enum CapKind {
  Cclose, Cposition, Cconst, Cbackref, Carg, Csimple, Ctable, Cfunction,
  Cquery, Cstring, Csubst, Cfold, Cruntime, Cgroup
} CapKind;
]]

ffi.cdef[[
typedef struct Capture {
long s;  /* position */
short idx;
byte kind;
byte siz;
} Capture;
]]

local FC = ffi.C

local maxstack = FC.MAXBACK

local function instsize(l) return math.floor(((l + ffi.sizeof('Instruction') - 1) / ffi.sizeof('Instruction') + 1)) end

local function testchar(st, c)
    return bit.band(st[bit.rshift(c, 3)], bit.lshift(1, bit.band(c, 7))) ~= 0
end

local CHARSETINSTSIZE = instsize(FC.CHARSETSIZE)

local function sizei(pat, n)
    local code = pat[n].code
    if code == FC.ISet or code == FC.ISpan then
        return CHARSETINSTSIZE
    elseif code == FC.IFunc then
        return pat[n].aux + 2
    else
        return 1
    end
end

--[[ DEBUG
local function printcapkind(cap)
    local modes = {
        "close", "position", "constant", "backref",
        "argument", "simple", "table", "function",
        "query", "string", "substitution", "fold",
        "runtime", "group"
    };
    return string.format("%s", modes[cap + 1])
end

local function printcap(cap, n)
    return printcapkind(cap[n].kind) .. string.format("(idx: %d - size: %d) -> %d\n", cap[n].idx, cap[n].siz, cap[n].s)
end

local function printcaplist(cap)
    local n = 0
    local ret = {}
    while cap[n].s ~= -1 do
        ret[n + 1] = n .. ' ' .. printcap(cap, n)
        n = n + 1
    end
    print(table.concat(ret))
end

local function printcharset(st, ret)
    ret[#ret + 1] = string.format("[")
    local i = 0
    while i <= FC.UCHAR_MAX do
        local first = i
        while testchar(st, i) and (i <= FC.UCHAR_MAX) do i = i + 1 end
        if (i - 1) == first then -- unary range?
            ret[#ret + 1] = string.format("(%02x)", first)
        elseif (i - 1) > first then -- non-empty range? */
            ret[#ret + 1] = string.format("(%02x-%02x)", first, i - 1)
        end
        i = i + 1
    end
    ret[#ret + 1] = string.format("]")
end

local function printjmp(p, n, ret)
    ret[#ret + 1] = "-> "
    if p[n].offset == 0 then
        ret[#ret + 1] = "FAIL"
    else
        ret[#ret + 1] = string.format("%d", p[n].offset + n)
    end
end

local function printinst(p, n)
    local names = {
        "any", "char", "set", "span", "back",
        "ret", "end",
        "choice", "jmp", "call", "open_call",
        "commit", "partial_commit", "back_commit", "failtwice", "fail", "giveup",
        "func",
        "fullcapture", "emptycapture", "emptycaptureidx", "opencapture",
        "closecapture", "closeruntime"
    }

    local ret = {}
    local code = p[n].code
    ret[#ret + 1] = string.format("%02d: %s ", n, names[code + 1])
    if code == FC.IChar then
        ret[#ret + 1] = string.format("'%c'", p[n].aux)
        printjmp(p, n, ret)
    elseif code == FC.IAny then
        ret[#ret + 1] = string.format("* %d", p[n].aux);
        printjmp(p, n, ret)
    elseif code == FC.IFullCapture or code == FC.IOpenCapture or
            code == FC.IEmptyCapture or code == FC.IEmptyCaptureIdx or
            code == FC.ICloseCapture or code == FC.ICloseRunTime then
        ret[#ret + 1] = printcapkind(bit.band(p[n].aux, 0xF))
        ret[#ret + 1] = string.format("(n = %d)  (off = %d)", bit.band(bit.rshift(p[n].x, 4), 0xF), p[n].fset)
    elseif code == FC.ISet then
        printcharset(p[n + 1].buff, ret)
        printjmp(p, n, ret)
    elseif code == FC.ISpan then
        printcharset(p[n + 1].buff, ret)
    elseif code == FC.IOpenCall then
        ret[#ret + 1] = string.format("-> %d", p[n].offset)
    elseif code == FC.IChoice then
        printjmp(p, n, ret)
        ret[#ret + 1] = string.format(" (%d)", p[n].aux)
    elseif code == FC.IJmp or code == FC.ICall or
            code == FC.ICommit or code == FC.IPartialCommit or
            code == FC.IBackCommit then
        printjmp(p, n, ret)
    end
    return table.concat(ret)
end

local function printpatt(pat)
    local n = 0
    local ret = {}
    local p = ffi.cast('Instruction*', pat)
    while true do
        ret[#ret + 1] = printinst(p, n)
        ret[#ret + 1] = '\n'
        if p[n].de == FC.IEnd then break end
        n = n + sizei(p, n)
    end
    print(table.concat(ret))
end
--]]

local patstable = setmetatable({}, { __mode = 'k' })

local function savepattern(name, pat)
    local file = assert(io.open(name, 'wb'))
    local p = ffi.cast('Instruction*', pat)
    local n = 0
    repeat
        local code = p[n].code
        local size = sizei(p, n)
        local data = ffi.string(p + n, size * ffi.sizeof('Instruction'))
        file:write(data)
        n = n + size
        until code == FC.IEnd
    file:close()
end

local function loadpattern(name)
    local file = io.open(name, 'rb')
    local data = file:read('*all')
    file:close()
    local pat = ffi.new('Instruction[?]', #data / ffi.sizeof('Instruction'))
    ffi.copy(pat, data, #data)
    local opat = ffi.cast('Instruction&', pat)
    patstable[opat] = pat
    return opat
end

local function retcount(...)
    return select('#', ...), { ... }
end

local pushallvalues, substcap, stringcap, pushcapture, nextcap, findopen

local function addonestring(buf, env, cap, dyncaps, str, n, args, argscount, what)
    local kind = cap[n].kind
    if kind == FC.Cstring then
        return stringcap(buf, env, cap, dyncaps, str, n, args, argscount) -- add capture directly to buffer TODO  check
    elseif kind == FC.Csubst then
        return substcap(buf, env, cap, dyncaps, str, n, args, argscount) -- add capture directly to buffer  TODO  check
    else
        local k
        local caps, capscount = {}
        n, k, capscount = pushcapture(env, cap, dyncaps, str, n, args, argscount, caps, 1)
        assert(k)
        if k > 0 then
            if type(caps[1]) ~= 'string' and type(caps[1]) ~= 'number' then
                error(string.format("invalid %s value (a %s)", what, type(caps[1])))
            end
            buf[#buf + 1] = caps[1]
        end
        return n, k
    end
end

function pushallvalues(env, cap, dyncaps, str, n, args, argscount, ret, retidx, addextra)
    local k = 0
    local start = n
    local startret = retidx
    if cap[n].siz ~= 0 then
        ret[retidx] = ffi.string(str + cap[n].s, cap[n].siz - 1) -- push whole match
        retidx = retidx + 1
        n = n + 1
        return n, 1, retidx
    end
    n = n + 1
    while cap[n].kind ~= FC.Cclose do
        local k1
        n, k1, retidx = pushcapture(env, cap, dyncaps, str, n, args, argscount, ret, retidx)
        k = k + k1
    end
    if addextra ~= 0 or k == 0 then -- need extra
        table.insert(ret, startret, ffi.string(str + cap[start].s, cap[n].s - cap[start].s)) -- push whole match
        retidx = retidx + 1
        k = k + 1
    end
    return n + 1, k, retidx -- skip close entry
end

function substcap(buf, env, cap, dyncaps, str, n, args, argscount)
    local curr = cap[n].s
    if cap[n].siz ~= 0 then -- no nested captures?
        buf[#buf + 1] = ffi.string(str + curr, cap[n].siz - 1) -- keep original text
    else
        n = n + 1
        while cap[n].kind ~= FC.Cclose do
            local next = cap[n].s;
            buf[#buf + 1] = ffi.string(str + curr, next - curr) -- add text up to capture
            local k
            n, k = addonestring(buf, env, cap, dyncaps, str, n, args, argscount, "replacement")
            --          assert(k)
            if k == 0 then
                curr = next -- keep original text in final result
            else
                curr = cap[n - 1].s + cap[n - 1].siz - 1 -- continue after match
            end
        end
        buf[#buf + 1] = ffi.string(str + curr, cap[n].s - curr) -- add last piece of text
    end
    return n + 1 -- go to next capture
end

local function getstrcaps(str, cap, n, cpsi, cps)
    local k = cpsi
    cpsi = cpsi + 1

    local s = cap[n].s
    if cap[n].siz == 0 then
        n = n + 1
        while cap[n].kind ~= FC.Cclose do
            if k >= FC.MAXSTRCAPS then -- too many captures?
                n = nextcap(cap, n) -- skip it
            elseif cap[n].kind == FC.Csimple then
                cpsi, n = getstrcaps(str, cap, n, cpsi, cps)
            else
                cps.caps[cpsi + 1] = n
                n = nextcap(cap, n)
                cpsi = cpsi + 1
            end
        end
    end
    n = n + 1
    cps.str[k + 1] = ffi.string(str + s, cap[n - 1].s + cap[n - 1].siz - s - 1)
    return cpsi, n
end

function stringcap(buf, env, cap, dyncaps, str, n, args, argscount)
    local caps
    local oc = env[cap[n].idx]
    local len = #oc
    local c = ffi.cast('const char *', oc)
    local cps = { str = {}, caps = {} }
    caps, n = getstrcaps(str, cap, n, 0, cps) --TODO
    caps = caps - 1
    local i = 0
    while i < len do
        if c[i] ~= 37 or c[i + 1] < 48 or c[i + 1] > 57 then
            if c[i] == 37 then i = i + 1 end
            buf[#buf + 1] = string.char(c[i])
        else
            i = i + 1
            local l = c[i] - 48
            if l > caps then
                error(string.format("invalid capture index (%d)", l))
            elseif cps.str[l + 1] then
                buf[#buf + 1] = cps.str[l + 1]
            else
                local k, _
                local locn = assert(cps.caps[l + 1])
                _, k = addonestring(buf, env, cap, dyncaps, str, locn, args, argscount, "capture") --TODO
                --              assert(k)
                if k == 0 then
                    error(string.format("no values in capture index %d", l))
                end
            end
        end
        i = i + 1
    end
    return n
end

function nextcap(cap, n)
    if cap[n].siz ~= 0 then
        return n + 1
    else
        local i = 0;
        while true do
            n = n + 1
            if cap[n].kind == FC.Cclose then
                if i == 0 then return n + 1 end
                i = i - 1
            elseif cap[n].siz == 0 then
                i = i + 1
            end
        end
    end
end

local function findback(env, cap, n, name)
    while true do
        if n == 0 then -- not found
            error(string.format("back reference '%s' not found", name))
        end
        n = n - 1
        if cap[n].kind == FC.Cclose then
            n = findopen(cap, n)
            if cap[n].kind == FC.Cgroup and name == env[cap[n].idx] then -- get group name right group?
                return n
            end
        elseif cap[n].siz ~= 0 then
            if cap[n].kind == FC.Cgroup and name == env[cap[n].idx] then -- get group name right group?
                return n
            end
        end
    end
end

local function backrefcap(env, cap, dyncaps, str, n, args, argscount, ret, retidx)
    local k
    local curr = n
    local name = assert(env[cap[n].idx]) -- reference name
    n = findback(env, cap, curr, name)
    n, k, retidx = pushallvalues(env, cap, dyncaps, str, n, args, argscount, ret, retidx, 0);
    n = curr + 1;
    return n, k, retidx
end

local function tablecap(env, cap, dyncaps, str, n, args, argscount, ret, retidx)
    local t = {}
    local tabidx = 1
    ret[retidx] = t
    retidx = retidx + 1
    if cap[n].siz ~= 0 then
        return n + 1, 1, retidx -- table is empty
    end
    n = n + 1
    while cap[n].kind ~= FC.Cclose do
        if cap[n].kind == FC.Cgroup and cap[n].idx ~= 0 then -- named group
            local k
            local gname = env[cap[n].idx] -- push group name
            local caps, capscount = {}
            n, k, capscount = pushallvalues(env, cap, dyncaps, str, n, args, argscount, caps, 1, 0)
            assert(k)
            if k > 0 then -- no value?
                t[gname] = caps[1]
            end
        else
            local k
            local caps, capscount = {}
            n, k, capscount = pushcapture(env, cap, dyncaps, str, n, args, argscount, caps, 1)
            assert(k)
            for i = 1, capscount - 1 do
                t[tabidx] = caps[i]
                tabidx = tabidx + 1
            end
        end
    end
    n = n + 1 -- skip close entry
    return n, 1, retidx
end

local function querycap(env, cap, dyncaps, str, n, args, argscount, ret, retidx)
    local k
    local t = env[cap[n].idx]
    local caps, capscount = {}
    n, k, capscount = pushallvalues(env, cap, dyncaps, str, n, args, argscount, caps, 1, 0);
    assert(k)
    local key = caps[1]
    if t[key] then
        ret[retidx] = t[key]
        retidx = retidx + 1
        return n, 1, retidx
    else
        return n, 0, retidx
    end
end

local function foldcap(env, cap, dyncaps, str, n, args, argscount, ret, retidx)
    local k
    local fce = env[cap[n].idx]
    if cap[n].siz == 0 then
        n = n + 1
        if cap[n].kind ~= FC.Cclose then
            local caps = {}
            n, k = pushcapture(env, cap, dyncaps, str, n, args, argscount, caps, 1)
            assert(k)
            if k > 0 then
                local first = caps[1]
                while cap[n].kind ~= FC.Cclose do
                    local caps, capscount = {}
                    n, k, capscount = pushcapture(env, cap, dyncaps, str, n, args, argscount, caps, 1) -- get other captures
                    first = fce(first, unpack(caps, 1, capscount - 1)) -- call folding function
                end
                n = n + 1 -- skip close entry
                ret[retidx] = first
                retidx = retidx + 1
                return n, 1, retidx
            end
        end
    end
    error("no initial value for fold capture")
end

local function functioncap(env, cap, dyncaps, str, n, args, argscount, ret, retidx)
    local k
    local cps, capscount = {}
    local fce = env[cap[n].idx]
    n, k, capscount = pushallvalues(env, cap, dyncaps, str, n, args, argscount, cps, 1, 0)
    assert(k)
    local capscount, caps = retcount(fce(unpack(cps, 1, capscount - 1)))
    for i = 1, capscount do
        ret[retidx] = caps[i]
        retidx = retidx + 1
    end
    return n, #caps, retidx
end

function pushcapture(env, cap, dyncaps, str, n, args, argscount, ret, retidx)
    local kind = cap[n].kind
    if kind == FC.Cposition then
        ret[retidx] = cap[n].s + 1
        retidx = retidx + 1
        return n + 1, 1, retidx
    elseif kind == FC.Cconst then
        ret[retidx] = env[cap[n].idx]
        retidx = retidx + 1
        return n + 1, 1, retidx
    elseif kind == FC.Carg then
        assert(cap[n].idx > 0 and cap[n].idx <= argscount, string.format("reference to absent argument #%d", cap[n].idx))
        ret[retidx] = args[cap[n].idx]
        retidx = retidx + 1
        return n + 1, 1, retidx
    elseif kind == FC.Csimple then
        return pushallvalues(env, cap, dyncaps, str, n, args, argscount, ret, retidx, 1)
    elseif kind == FC.Cruntime then
        local k = 0
        while cap[n].kind ~= FC.Cclose do
            --       luaL_checkstack(cs->L, 4, "too many captures");
            --       lua_pushvalue(cs->L, (cs->cap - 1)->idx);
            ret[retidx] = dyncaps[cap[n].idx]
            retidx = retidx + 1
            n = n + 1
            k = k + 1
        end
        return n + 1, k, retidx
    elseif kind == FC.Cstring then
        local buf = {}
        n = stringcap(buf, env, cap, dyncaps, str, n, args, argscount)
        ret[retidx] = table.concat(buf)
        retidx = retidx + 1
        return n, 1, retidx
    elseif kind == FC.Csubst then
        local buf = {}
        n = substcap(buf, env, cap, dyncaps, str, n, args, argscount)
        ret[retidx] = table.concat(buf)
        retidx = retidx + 1
        return n, 1, retidx
    elseif kind == FC.Cgroup then
        if cap[n].idx == 0 then -- anonymous group?
            return pushallvalues(env, cap, dyncaps, str, n, args, argscount, ret, retidx, 0) -- add all nested values
        else -- named group: add no values
            n = nextcap(cap, n) -- skip capture
            return n, 0, retidx
        end
    elseif kind == FC.Cbackref then
        return backrefcap(env, cap, dyncaps, str, n, args, argscount, ret, retidx)
    elseif kind == FC.Ctable then
        return tablecap(env, cap, dyncaps, str, n, args, argscount, ret, retidx)
    elseif kind == FC.Cfunction then
        return functioncap(env, cap, dyncaps, str, n, args, argscount, ret, retidx)
    elseif kind == FC.Cquery then
        return querycap(env, cap, dyncaps, str, n, args, argscount, ret, retidx)
    elseif kind == FC.Cfold then
        return foldcap(env, cap, dyncaps, str, n, args, argscount, ret, retidx)
    else
        assert(false)
    end
end

local function getcaptures(env, str, i, cap, dyncaps, args, argscount)
    local n = 0
    local k = 0
    local ret = {}
    local retidx = 1
    while cap[n].kind ~= FC.Cclose do --is there any capture
        local k1
        n, k1, retidx = pushcapture(env, cap, dyncaps, str, n, args, argscount, ret, retidx)
        k = k + k1
    end
    return i, ret, retidx
end

function findopen(cap, c)
    local n = 0;
    while true do
        c = c - 1
        if cap[c].kind == FC.Cclose then
            n = n + 1
        elseif cap[c].siz == 0 then
            if n == 0 then return c
            end
            n = n - 1
        end
    end
end

local function runtimecap(env, str, s, i, cap, dyncaps, c, args, argscount)
    local open = findopen(cap, c)
    assert(cap[open].kind == FC.Cruntime)
    cap[c].kind = FC.Cclose;
    cap[c].s = i
    local captures, capscount = {}
    local n, k, capscount = pushallvalues(env, cap, dyncaps, str, open, args, argscount, captures, 1, 0)
    assert(k)
    return c - open, retcount(env[cap[open].idx](s, i + 1, unpack(captures, 1, capscount - 1)))
end

local function adddyncaptures(s, cap, c, dyncaps, dyncapscount, outcaps, outcapscount)
    --  assert(cap[c].kind == FC.Cruntime and cap[c].siz == 0)
    cap[c].idx = dyncapscount -- first returned capture
    dyncaps[dyncapscount] = outcaps[1]
    dyncapscount = dyncapscount + 1
    for i = 1, outcapscount - 1 do -- add extra captures
        cap[c + i] = { s, dyncapscount, FC.Cruntime, 1 } -- mark it as closed
        dyncaps[dyncapscount] = outcaps[i + 1]
        dyncapscount = dyncapscount + 1
    end
    c = c + outcapscount
    cap[c] = { s, 0, FC.Cclose, 1 } -- add closing entry
    return c + 1, dyncapscount
end

local function setmaxstack(limit)
    maxstack = limit
end

local function match(o, s, init, ...)
    local IGiveup = {}
    local cap = ffi.new('Capture[?]', FC.INITCAPSIZE)
    local capsize = FC.INITCAPSIZE
    local stacklimit = FC.INITBACK
    init = init or 1
    init = init < 0 and #s + init + 1 or init
    init = init < 1 and 1 or init
    local argscount, args = retcount(...)
    local len = #s
    local str = ffi.cast('byte*', s)
    local opat = ffi.istype('Instruction', o) and o or lpeg.P(o)
    local env = debug.getfenv(opat)
    local pat = ffi.cast('Instruction*', opat)
    local i = (init or 1) - 1
    local p = 0
    local c = 0

    local e = {}
    e[#e + 1] = { p = IGiveup; i = i; c = c }
    e[#e + 1] = {}
    local dyncaps, dyncapscount = {}, 1

    local function doublestack()
        if stacklimit >= maxstack then
            error("too many pending calls/choices")
        end
        local newn = 2 * stacklimit; if (newn > maxstack) then newn = maxstack end
        stacklimit = newn
    end

    local function doublecap()
        local newcap = ffi.new('Capture[?]', capsize * 2)
        ffi.copy(newcap, cap, c * ffi.sizeof('Capture'))
        cap = newcap
        capsize = capsize * 2
    end

    local function capture(size)
        cap[c].s = i - bit.band(bit.rshift(pat[p].aux, 4), 0xF)
        cap[c].idx = pat[p].offset;
        cap[c].kind = bit.band(pat[p].aux, 0xF)
        cap[c].siz = size
        c = c + 1
        if c + 1 >= capsize then doublecap() end
        p = p + 1
    end

    local function fail()
        repeat
            e[#e] = nil
            i = e[#e].i
            until i
        c = e[#e].c
        p = e[#e].p
    end

    local function condfailed()
        local f = pat[p].offset
        if f ~= 0 then
            p = p + f
        else
            fail()
        end
    end

    while true do
        if p == IGiveup then return nil end
        --      print(printinst(pat,p))
        local code = pat[p].code
        if code == FC.IEnd then
            cap[c].kind = FC.Cclose;
            cap[c].s = -1
            --          printcaplist(cap)
            local i, ret, retidx = getcaptures(env, str, i, cap, dyncaps, args, argscount)
            if retidx == 1 then
                return i + 1
            else
                return unpack(ret, 1, retidx - 1)
            end
        elseif code == FC.IAny then
            local n = pat[p].aux
            if n <= len - i then
                p = p + 1
                i = i + n
            else
                condfailed()
            end
        elseif code == FC.IChar then
            if str[i] == pat[p].aux and i < len then
                p = p + 1
                i = i + 1
            else
                condfailed()
            end
        elseif code == FC.ISet then
            if testchar(pat[p + 1].buff, str[i]) and i < len then
                p = p + CHARSETINSTSIZE;
                i = i + 1;
            else
                condfailed()
            end
        elseif code == FC.IBack then
            local n = pat[p].aux
            if n > i then
                fail()
            else
                i = i - n
                p = p + 1
            end
        elseif code == FC.IRet then
            e[#e] = nil
            p = e[#e].p
        elseif code == FC.IFunc then
            local r = pat[p + 1].f(str + i, str + i + len, str + init - 1, pat[p + 2].buff)
            if r ~= nil then
                i = r - str
                p = p + pat[p].aux + 2
            else
                condfailed()
            end
        elseif code == FC.ISpan then
            while i < len do
                if not testchar(pat[p + 1].buff, str[i]) then break
                end
                i = i + 1
            end
            p = p + CHARSETINSTSIZE
        elseif code == FC.IJmp then
            p = p + pat[p].offset
        elseif code == FC.IChoice then
            if #e - 1 == stacklimit then
                doublestack()
            end
            e[#e].p = p + pat[p].offset
            e[#e].i = i - pat[p].aux
            e[#e].c = c
            e[#e + 1] = {}
            p = p + 1
        elseif code == FC.ICommit then
            e[#e] = nil
            e[#e] = {}
            p = p + pat[p].offset;
        elseif code == FC.IPartialCommit then
            e[#e - 1].i = i
            e[#e - 1].c = c
            p = p + pat[p].offset;
        elseif code == FC.IBackCommit then
            e[#e] = nil
            i = e[#e].i
            c = e[#e].c
            e[#e] = {}
            p = p + pat[p].offset
        elseif code == FC.ICall then
            if #e - 1 == stacklimit then
                doublestack()
            end
            --          e[#e] = { p = p + 1 }
            e[#e].p = p + 1
            e[#e + 1] = {}
            p = p + pat[p].offset;
        elseif code == FC.IFailTwice then
            e[#e] = nil
            fail()
        elseif code == FC.IFail then
            fail()
        elseif code == FC.IEmptyCapture or code == FC.IEmptyCaptureIdx then
            capture(1) -- mark entry as closed
        elseif code == FC.IOpenCapture then
            capture(0) -- mark entry as open
        elseif code == FC.ICloseCapture then
            local s1 = i - bit.band(bit.rshift(pat[p].aux, 4), 0xF)
            if cap[c - 1].siz == 0 and s1 - cap[c - 1].s < FC.UCHAR_MAX then
                cap[c - 1].siz = s1 - cap[c - 1].s + 1
                p = p + 1
            else
                capture(1) -- mark entry as closed
            end
        elseif code == FC.IFullCapture then
            capture(bit.band(bit.rshift(pat[p].aux, 4), 0xF) + 1) -- save capture size
        elseif code == FC.IOpenCall then
            error(string.format("reference to %s outside a grammar", string.format("rule '%s'", env[pat[p].offset])))
        elseif code == FC.ICloseRunTime then
            local inpcap, retcount, retout = runtimecap(env, str, s, i, cap, dyncaps, c, args, argscount)
            local res = retout[1]
            if res then
                local outcaps = { unpack(retout, 2, retcount) }
                retcount = retcount - 1
                --              assert(retcount >= 0)
                if type(res) == 'number' then
                    assert(res > i and res <= len + 1, "invalid position returned by match-time capture")
                    i = res - 1
                    --              else
                    --                  assert(type(res) == 'boolean')
                end
                c = c - inpcap
                --              assert(c >= 0)
                if retcount > 0 then -- captures?
                    if c + retcount + 1 + 1 >= capsize then
                        doublecap()
                    end
                    c, dyncapscount = adddyncaptures(i, cap, c, dyncaps, dyncapscount, outcaps, retcount)
                end
                p = p + 1
            else
                fail()
            end
        else
            assert(false)
        end
    end
end

--ffi.metatype('Instruction', { __index = lpeg })

lpeg.match = match
lpeg.setmaxstack = setmaxstack

return lpeg

