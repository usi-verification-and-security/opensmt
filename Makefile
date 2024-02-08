BUILD_DIR_BASE = build
RELEASE_BUILD_DIR = $(BUILD_DIR_BASE)
DEBUG_BUILD_DIR = $(BUILD_DIR_BASE)-debug

INSTALL_DIR = /usr/local

CMAKE_FLAGS += -DCMAKE_INSTALL_PREFIX=$(INSTALL_DIR)
RELEASE_CMAKE_FLAGS = $(CMAKE_FLAGS)
DEBUG_CMAKE_FLAGS = $(CMAKE_FLAGS) -DCMAKE_BUILD_TYPE=Debug

################################################################

.PHONY: default all release debug
.PHONY: _dir-release _dir-debug _build-release _build-debug

default: release

all: release debug

release: _dir-release _build-release

_dir-release: $(RELEASE_BUILD_DIR)

_build-release: | $(RELEASE_BUILD_DIR)
	cmake --build $(RELEASE_BUILD_DIR)

$(RELEASE_BUILD_DIR):
	cmake -B $(RELEASE_BUILD_DIR) $(RELEASE_CMAKE_FLAGS)

debug: _dir-debug _build-debug

_dir-debug: $(DEBUG_BUILD_DIR)

_build-debug: | $(DEBUG_BUILD_DIR)
	cmake --build $(DEBUG_BUILD_DIR)

$(DEBUG_BUILD_DIR):
	cmake -B $(DEBUG_BUILD_DIR) $(DEBUG_CMAKE_FLAGS)

################################

.PHONY: clean clean-all clean-release clean-debug

clean: clean-release

clean-all: clean-release clean-debug

clean-release:
	rm -fr $(RELEASE_BUILD_DIR)

clean-debug:
	rm -fr $(DEBUG_BUILD_DIR)

################################

.PHONY: install install-release install-debug

install: install-release

install-release: release
	$(MAKE) -C $(RELEASE_BUILD_DIR) install

install-debug: debug
	$(MAKE) -C $(DEBUG_BUILD_DIR) install
