VERSION = 0.1

DOC = lua52vm.html 
CODE = bytecode.lua vm52.lua

package: $(DOC) $(CODE)
	zip -u zip/lua52bytecode_and_vm-$(VERSION).zip $(DOC) $(CODE) 

luavm52.html: doc/lua52vm.txt
	make -C doc
