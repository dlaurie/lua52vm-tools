-- bytecode.lua
-- Bytecode Hacks  (c) 2013 Dirk Laurie  Lua-like MIT license

-- Returns a function that turns a binary chunk into hacked bytecode.
-- Example:
--
-- bytecode = require"bytecode"
-- chunk = io.open("luac.out","rb"):read("*a")
-- chunk = string.dump(load "local x,y = ...; return x+y,select(3,...)")
-- code = bytecode(chunk)
-- f=code.instr -- table containing instructions of the main function
-- print(#f) -- the number of instructions
-- print(string.format("%08X",f[1]))  -- the first instruction
-- vm = require"vm52"
-- for k,instr in ipairs(f) do print(vm.disassemble(instr)) end
--> VARARG 0 3
--> ADD 2 0 1
--> GETTABUP 3 0 -1
--> LOADK 4 -2
--> VARARG 5 0
--> CALL 3 0 0
--> RETURN 2 0
--> RETURN 0 1
-- f[1] = vm.assemble"move 1 2"  -- replace the first instruction
-- also possible: table.insert(f,instr) etc
-- chunk1 = tostring(code) -- binary chunk containing hacked bytecode
--
-- BUGS
--    1. Can't handle constants, prototypes, upvalues. Some code
--       provided but not actually used yet.
--    2. Does not update nregs to take account hacked instructions.
--    3. Not tested outside a system with myint = myinstr = mysize = 4,
--       probably does not work then.
--    4. Not tested on a big-endian system.

-- functions applicable to a bytecode header
local header = function(code) return code:sub(1,18) end
local lua52 = function(code) return code:sub(1,6) end
local bigendian =  function(code) return code:byte(7,7)==0 end
local intlen = function(code) return code:byte(8,8) end
local sizelen = function(code) return code:byte(9,9) end
local instrlen = function(code) return code:byte(10,10) end
local numlen = function(code) return code:byte(11,11) end
local usesfloat = function(code) return code:byte(12,12)==0 end
local tail = function(code) return code:sub(13,18) end
local skip = function(code) return code:sub(19,-1) end
local istart = 19

-- parameters of the host system
local voidfunc = string.dump(load"")
local myendian = bigendian(voidfunc)
local myint = intlen(voidfunc)
local myinstr = instrlen(voidfunc)
local mysize = sizelen(voidfunc)
local mynum = numlen(voidfunc)
local myfloat = usesfloat(voidfunc)
local istop = istart+myint
local iupvals = istop+myint
local ivararg = iupvals+1
local iregs = ivararg+1
local iops = iregs+1
local iinstr = iops+myint

-- returns a number  
local function numberAt(str,idx,len)
   idx=idx or 1
   len=len or myint
   local bytes = str:sub(idx,idx+len-1)
   if not myendian then bytes=bytes:reverse() end
   local n=0
   for k=1,len do n=bit32.lshift(n,8)+bytes:byte(k,k) end
   return n
end 

-- turns number back into bytes
local function bytes(instr)
   local bytes={}
   for k=1,myinstr do bytes[k]=bit32.extract(instr,8*(k-1),8) end
   if myendian then return string.char(unpack(bytes)):reverse()
   else return string.char(unpack(bytes))
   end
end

-- returns string with length word and trailing zero byte
local function stringAt(str,idx)
   idx = idx or 1
   return str:sub(idx,idx+mysize+numberAt(str,idx+1))
end

-- constant, any of four types, as stored in bytecode
--   returns decoded value and also the actual bytes
local CTYPE = {NIL=0, BOOL=1, NUM=3, STR=4}
local function constAt(code,idx) 
   local ctype = code:byte(idx,idx)
   if ctype == CTYPE.NIL then return nil, code:sub(idx,idx)
   elseif ctype == CTYPE.BOOL then 
      local bool=code:sub(idx,idx+1)
      return byte(bool)>0, bool
   elseif ctype == CTYPE.NUM then 
      local num=sub(idx,idx+numsize)
      if uses_float then error("Not supported: floating-point constants")
      else return numberAt(num), num 
      end
   elseif ctype == CTYPE.STR then 
      local str=stringAt(code,idx)
      return str:sub(mysize+1,-2), str
   end
end

-- functions applicable to a function header
local nstart = function(code) return numberAt(code,istart) end
local nstop = function(code) return numberAt(code,istop) end
local nupvals = function(code) return code:byte(iupvals) end
local usesvararg = function(code) return code:byte(ivararg)>0 end
local nregs = function(code) return code:byte(iregs) end
local nops = function(code) return numberAt(code,iops) end

-- functions applicable to a function body
local instr = function(code)
   local ops = {}
   for k=1,nops(code) do ops[k] = numberAt(code,iinstr+(k-1)*myint) end
   return ops
   end

local update=function(str,pos,repl)
   return str:sub(1,pos-1)..repl..str:sub(pos+#repl,-1)
end

local konkat=function(tbl)
   local t={}
   for k,v in ipairs(tbl) do t[k]=bytes(v) end
   return table.concat(t)
end

local mt = {
  __tostring = function(self) 
    local code=update(self.chunk,iops,string.char(#self.instr))   
    return code:sub(1,iinstr-1)..konkat(self.instr)..
           code:sub(iinstr+myinstr*nops(self.chunk),-1)
  end
}

local bytecode = function(chunk)
   if not (lua52(chunk)==lua52(voidfunc) and 
           tail(chunk)==tail(voidfunc)) then error 
      "bytecode error: chunk is not genuine Lua 5.2 bytecode" 
   end    
   if not header(chunk)==header(voidfunc) then error 
      "bytecode error: chunk was not compiled on a compatible machine"
   end
   local code = {chunk=chunk; instr=instr(chunk)}
   setmetatable(code,mt)
   return code
end
       
return bytecode

