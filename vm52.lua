-- vm52.lua  (c) Dirk Laurie 2013  Lua-style MIT licence
-- Relying heavily on Lua 5.2 (c) 1994-2012 Lua.org, PUC-Rio

-- The module returns a table of functions.
-- 
-- instr, bytes = vm52.assemble(str)
--    returns the bytecode of the instruction in "str" as a 32-bit number 
--    and as a 4-byte string. The opname is not case-sensitive.
--  
-- nameargs = vm52.disassemble(bytecode)
--    reverses the effect of `assemble` (either `instr` or `bytes`).
--
-- instr = vm52.numberAt(str,pos)
--    converts the 4-byte string at position `pos` (default 1) of `str` 
--    into a number, taking endian-ness into account.
-- 
-- bytes = vm52.bytes(instr)
--    converts a 32-bit number into a 4-byte string, taking endian-ness 
--    into account
--
-- The table also contains functions for each opname, with Lua-style
-- argument lists. The opname must be in uppercase and the error messages 
-- are less user-friendly than those given by `assemble`.

-- aliases for routines from standard libraries
local SHL = bit32.lshift
local NOT = bit32.bnot
local OR = bit32.bor
local AND = bit32.band
local EXT = bit32.extract
local concat, unpack = table.concat, table.unpack
local char, dump, reverse = string.char, string.dump, string.reverse

-- instruction types, opnames and opcodes

local iA, iAB, iAC, iABC, iAx, iABx, iAsBx =
     "iA", "iAB", "iAC", "iABC", "iAx", "iABx", "iAsBx"

local op = { 
-- Loading of constants
  [1]={LOADK=iABx}, [2]={LOADKX=iA}, [39]={EXTRAARG=iAx},
-- Unary functions
  [0]={MOVE=iAB}, [19]={UNM=iAB}, [20]={NOT=iAB}, [21]={LEN=iAB}, 
-- Binary functions
  [13]={ADD=iABC}, [14]={SUB=iABC}, [15]={MUL=iABC}, 
  [16]={DIV=iABC}, [17]={MOD=iABC}, [18]={POW=iABC}, 
-- Table access
  [7]={GETTABLE=iABC}, [10]={SETTABLE=iABC}, [11]={NEWTABLE=iABC},
  [12]={SELF=iABC}, [36]={SETLIST=iABC}, 
-- Dealing with tuples
  [4]={LOADNIL=iAB}, [22]={CONCAT=iABC}, [38]={VARARG=iAB}, 
  [29]={CALL=iABC}, [30]={TAILCALL=iABC}, [34]={TFORCALL=iAC}, 
  [31]={RETURN=iAB}, 
-- Interaction with upvalues
  [5]={GETUPVAL=iAB}, [9]={SETUPVAL=iAB}, 
  [6]={GETTABUP=iABC}, [8]={SETTABUP=iABC},
 -- Logical functions
  [3]={LOADBOOL=iABC}, [27]={TEST=iAC}, [28]={TESTSET=iABC},
  [24]={EQ=iABC}, [25]={LT=iABC}, [26]={LE=iABC},  
-- Branches, loops and closures
  [23]={JMP=iAsBx}, [37]={CLOSURE=iABx}, 
  [32]={FORLOOP=iAsBx}, [33]={FORPREP=iAsBx}, [35]={TFORLOOP=iAsBx}, 
}
-- Lua idiom: tables with only one key-value pair, as above, are
-- accessed by `next`, i.e.  
--    key, value = next(tbl)
-- Only `key` survives in contexts that can't use multiple values.

local opcodes = {}
for k=0,#op do opcodes[next(op[k])]=k end

-- stuff borrowed almost verbatim from lopcodes.h and lopcodes.c

--[===========================================================================[
  We assume that instructions are unsigned numbers.
  All instructions have an opcode in the first 6 bits.
  Instructions can have the following fields:
        `A' : 8 bits
        `B' : 9 bits
        `C' : 9 bits
        'Ax' : 26 bits ('A', 'B', and 'C' together)
        `Bx' : 18 bits (`B' and `C' together)
        `sBx' : signed Bx

  A signed argument is represented in excess K; that is, the number
  value is the unsigned value minus K. K is exactly the maximum value
  for that argument (so that -max is represented by 0, and +max is
  represented by 2*max), which is half the maximum for the corresponding
  unsigned argument.
]===========================================================================]

local SIZE, POS = {}, {}
SIZE.C = 9
SIZE.B = 9
SIZE.Bx = (SIZE.C + SIZE.B)
SIZE.A = 8
SIZE.Ax = (SIZE.C + SIZE.B + SIZE.A)
SIZE.OP = 6

POS.OP = 0
POS.A = (POS.OP + SIZE.OP)
POS.C = (POS.A + SIZE.A)
POS.B = (POS.C + SIZE.C)
POS.Bx = POS.C
POS.Ax = POS.A

-- end of stuff from lopcodes.*

-- Functions that assemble or disassemble operands in an instruction.
-- Both functions are called with only one pair {Reg=Val}

local function PUT(RegVal)
   local A,R = next(RegVal)
   return AND(SHL(R,POS[A]),NOT(SHL(-1,SIZE[A]+POS[A])))
end

local function GET(RegVal)
   local A,R = next(RegVal) 
   return EXT(R,POS[A],SIZE[A])
end

-- Decoding and encoding the various registers

local mB = SHL(1,SIZE.B-1)-1
local msBx = SHL(1,SIZE.Bx-1)-1
local function bias(B) if B<0 then return mB-B else return B end end
local function unbias(B) if B>mB then return mB-B else return B end end

get, put = {}, {}

get.A = function(instr) return GET{A=instr} end
put.A = function(field) return PUT{A=field} end

get.Ax = function(instr) return -1-GET{Ax=instr} end
put.Ax = function(field) return PUT{Ax=-1-field} end

get.B = function (instr) return unbias(GET{B=instr}) end
put.B = function(field) return PUT{B=bias(field)} end

get.Bx = function(instr) return -1-GET{Bx=instr} end
put.Bx = function(field) return PUT{Bx=-1-field} end

get.sBx = function(instr) return msBx-GET{Bx=instr} end
put.sBx = function(field) return PUT{Bx=msBx-field} end 

get.C = function (instr) return unbias(GET{C=instr}) end
put.C = function(field) return PUT{C=bias(field)} end

-- function table by optype

local REGS = {}
local INSTR = {}
for _,optype in pairs{iA, iAB, iAC, iABC, iAx, iABx, iAsBx} do
   local regs={}
   for reg in optype:gmatch"%u%l*" do regs[#regs+1]=reg end
   REGS[optype]=regs
   INSTR[optype] = function(opcode,...)
      local args={...}
      if #args~=#regs then error("Bad number of arguments to '"..
         next(op[opcode]).. "' (optype "..optype..
         "): expected "..#regs..", got "..#args) 
      end
      for k,reg in ipairs(regs) do 
         opcode=OR(opcode,put[reg](args[k]))
      end
      return opcode
   end   
end

-- function table per opname

local vm={}

for opcode=0,#op do 
   local opname, optype = next(op[opcode])
   vm[opname]=function(...) return INSTR[optype](opcode,...) end
end

--
  
local bigendian = dump(load""):sub(7,7)==0

local function bytecode(instr)
   local bytes={}
   for k=1,4 do bytes[k]=EXT(instr,8*(k-1),8) end
   if bigendian then return reverse(char(unpack(bytes)))
   else return char(unpack(bytes))
   end
end

local function numberAt(str,idx)
   idx=idx or 1
   local a,b,c,d = str:byte(idx,idx+3)
   if bigendian then a,b,c,d = d,c,b,a end
   return a+256*(b+256*(c+256*d))
end 
   
vm.assemble = function(nameargs)
   local name, args = nameargs:match("^(%a+)%s+(.+)$")
   if not args then 
      error("Improperly formed instruction: '"..nameargs.."'") 
   end
   local opcode = opcodes[name:upper()]
   if not opcode then error("Unknown instruction: '"..name.."'") end
   local _,optype = next(op[opcode])
   local arg={}
   for a in args:gmatch("%S+") do 
      local n=tonumber(a)
      if not n then error("Non-numeric argument to assemble: '"..a.."'") end
      arg[#arg+1]=n 
   end
   local instr = INSTR[optype](opcode,table.unpack(arg))
   return instr, bytecode(instr)
end

vm.disassemble = function(instr)
   if type(instr)=='string' and #instr==4 then instr=numberAt(instr) end
   if type(instr)~='number' then error(
      "Bad argument to disassemble: expected number, got "..type(string))
   end
   local opcode=GET{OP=instr}
   local opdef=op[opcode]
   if not opdef then error(
      "Bad argument to disassemble: invalid opcode "..opcode)
   end
   local name, optype = next(opdef)
   local regs = REGS[optype]
   local args={}
   for k,reg in pairs(regs) do args[k]=get[reg](instr) end
   return ("%s %s"):format(name,concat(args,' '))
end    

vm.bytes, vm.numberAt = bytecode, numberAt

function vm.hasvarargs(chunk) return chunk:sub(28,28):byte()>0 end
function vm.nstack(chunk) return chunk:sub(29,29):byte() end
function vm.ninstr(chunk) return vm52.numberAt(chunk,30) end
function vm.instr(chunk,i) return vm52.numberAt(chunk:sub(30+4*i,33+4*i)) end

return vm

--[[
$ lua -l vm52

print(string.format("%08X",vm52.assemble"gettabup 1 0 -2"))
--> 00404046

print(vm52.disassemble(vm52.assemble"gettabup 1 0 -2")) 
-->  GETTABUP 1 0 -2

print(vm52.disassemble(vm52.GETTABUP(1,0,-2))) 
-->  GETTABUP 1 0 -2

code = string.dump(load"x=2*y")
number_of_ops = vm52.numberAt(code,30)
print(number_of_ops)
--> 4
for i=1,number_of_ops do
   print(vm52.disassemble(code:sub(30+4*i,33+4*i)))
end  
--> GETTABUP 0 0 -2
--> MUL 0 -3 0
--> SETTABUP 0 -1 0
--> RETURN 0 1

--]]


