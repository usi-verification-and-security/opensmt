BUILD_DIR_BASE = build
## These can be customized via command line
RELEASE_BUILD_DIR = $(BUILD_DIR_BASE)
DEBUG_BUILD_DIR = $(BUILD_DIR_BASE)-debug

DEFAULT_INSTALL_DIR := /usr/local
USER_INSTALL_DIR := $(INSTALL_DIR)
## This can be customized via command line,
## it takes effect within both `cmake --build` and `cmake --install`
INSTALL_DIR = $(DEFAULT_INSTALL_DIR)

## These can be customized via command line
## Arguments for `cmake -B <build_dir>`
CMAKE_FLAGS += -DCMAKE_INSTALL_PREFIX=$(INSTALL_DIR)
RELEASE_CMAKE_FLAGS += $(CMAKE_FLAGS)
DEBUG_CMAKE_FLAGS += $(CMAKE_FLAGS) -DCMAKE_BUILD_TYPE=Debug

## These can be customized via command line
## Arguments for `cmake --build <build_dir>`
CMAKE_BUILD_FLAGS +=
RELEASE_CMAKE_BUILD_FLAGS += $(CMAKE_BUILD_FLAGS)
DEBUG_CMAKE_BUILD_FLAGS += $(CMAKE_BUILD_FLAGS)

## These can be customized via command line
## Arguments for `cmake --install <build_dir>`
CMAKE_INSTALL_FLAGS +=
ifneq ($(USER_INSTALL_DIR),)
  CMAKE_INSTALL_FLAGS += --prefix=$(USER_INSTALL_DIR)
endif
RELEASE_CMAKE_INSTALL_FLAGS += $(CMAKE_INSTALL_FLAGS)
DEBUG_CMAKE_INSTALL_FLAGS += $(CMAKE_INSTALL_FLAGS)

################################################################

.PHONY: default all release debug
.PHONY: _dir-release _dir-debug _build-release _build-debug

default: release

all: release debug

release: _dir-release _build-release

_dir-release: $(RELEASE_BUILD_DIR)

_build-release: _dir-release
	cmake --build $(RELEASE_BUILD_DIR) $(RELEASE_CMAKE_BUILD_FLAGS)

$(RELEASE_BUILD_DIR):
	cmake -B $(RELEASE_BUILD_DIR) $(RELEASE_CMAKE_FLAGS)

debug: _dir-debug _build-debug

_dir-debug: $(DEBUG_BUILD_DIR)

_build-debug: _dir-debug
	cmake --build $(DEBUG_BUILD_DIR) $(DEBUG_CMAKE_BUILD_FLAGS)

$(DEBUG_BUILD_DIR):
	cmake -B $(DEBUG_BUILD_DIR) $(DEBUG_CMAKE_FLAGS)

################################

.PHONY: test test-all test-release test-debug

test: test-release

test-all: test-release test-debug

test-release:
	ctest --test-dir $(RELEASE_BUILD_DIR)

test-debug:
	ctest --test-dir $(DEBUG_BUILD_DIR)

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
	cmake --install $(RELEASE_BUILD_DIR) $(RELEASE_CMAKE_INSTALL_FLAGS)

install-debug: debug
	cmake --install $(DEBUG_BUILD_DIR) $(DEBUG_CMAKE_INSTALL_FLAGS)
