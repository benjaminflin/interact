AGDA ?= agda
LIB_SOURCES := $(shell find src -name "*.agda")
APP_SOURCES := $(shell find app -name "*.agda")
COMPILE_DIR = out 
FLAGS = -i .
out ?= $(INSTALL_PREFIX)


.PHONY: app  
app: $(APP_SOURCES) 
	$(AGDA) $(FLAGS) $(APP_SOURCES) -c --compile-dir=$(COMPILE_DIR)

.PHONY: interact
interact: $(LIB_SOURCES)
	$(AGDA) $(FLAGS) $(LIB_SOURCES) -c --compile-dir=$(COMPILE_DIR)

.PHONY: install
install: app
	mkdir -p $(out)/bin
	install out/Main $(out)/bin/interact 

.PHONY: clean
clean:
	rm -rf _build $(COMPILE_DIR) 
