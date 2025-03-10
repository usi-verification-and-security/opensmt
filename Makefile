### This is just a wrapper Makefile script on top of CMake

BUILD_DIR_BASE = build

RELEASE_BUILD_DIR_SUFFIX =
DEBUG_BUILD_DIR_SUFFIX = -debug
## These can be customized via command line
RELEASE_BUILD_DIR = $(BUILD_DIR_BASE)$(RELEASE_BUILD_DIR_SUFFIX)
DEBUG_BUILD_DIR = $(BUILD_DIR_BASE)$(DEBUG_BUILD_DIR_SUFFIX)

PARALLEL_BUILD_DIR_SUFFIX = -parallel
## These can be customized via command line
PARALLEL_RELEASE_BUILD_DIR = $(BUILD_DIR_BASE)$(PARALLEL_BUILD_DIR_SUFFIX)$(RELEASE_BUILD_DIR_SUFFIX)
PARALLEL_DEBUG_BUILD_DIR = $(BUILD_DIR_BASE)$(PARALLEL_BUILD_DIR_SUFFIX)$(DEBUG_BUILD_DIR_SUFFIX)

DEFAULT_INSTALL_DIR := /usr/local
USER_INSTALL_DIR := $(INSTALL_DIR)
## This can be customized via command line,
## it takes effect within both `cmake --build` and `cmake --install`
INSTALL_DIR = $(DEFAULT_INSTALL_DIR)

## These can be customized via command line
## Arguments for `cmake -B <build_dir>`
CMAKE_FLAGS += -DCMAKE_INSTALL_PREFIX=$(INSTALL_DIR)

RELEASE_ONLY_CMAKE_FLAGS +=
DEBUG_ONLY_CMAKE_FLAGS += -DCMAKE_BUILD_TYPE=Debug
RELEASE_CMAKE_FLAGS += $(CMAKE_FLAGS) $(RELEASE_ONLY_CMAKE_FLAGS)
DEBUG_CMAKE_FLAGS += $(CMAKE_FLAGS) $(DEBUG_ONLY_CMAKE_FLAGS)

PARALLEL_ONLY_CMAKE_FLAGS += -DPARALLEL:BOOL=ON
PARALLEL_RELEASE_CMAKE_FLAGS += $(CMAKE_FLAGS) $(RELEASE_ONLY_CMAKE_FLAGS) $(PARALLEL_ONLY_CMAKE_FLAGS)
PARALLEL_DEBUG_CMAKE_FLAGS += $(CMAKE_FLAGS) $(DEBUG_ONLY_CMAKE_FLAGS) $(PARALLEL_ONLY_CMAKE_FLAGS)

## These can be customized via command line
## Arguments for `cmake --build <build_dir>`
CMAKE_BUILD_FLAGS +=

RELEASE_ONLY_CMAKE_BUILD_FLAGS +=
DEBUG_ONLY_CMAKE_BUILD_FLAGS +=
RELEASE_CMAKE_BUILD_FLAGS += $(CMAKE_BUILD_FLAGS) $(RELEASE_ONLY_CMAKE_BUILD_FLAGS)
DEBUG_CMAKE_BUILD_FLAGS += $(CMAKE_BUILD_FLAGS) $(DEBUG_ONLY_CMAKE_BUILD_FLAGS)

PARALLEL_ONLY_CMAKE_BUILD_FLAGS +=
PARALLEL_RELEASE_CMAKE_BUILD_FLAGS += $(CMAKE_BUILD_FLAGS) $(RELEASE_ONLY_CMAKE_BUILD_FLAGS) $(PARALLEL_ONLY_CMAKE_BUILD_FLAGS)
PARALLEL_DEBUG_CMAKE_BUILD_FLAGS += $(CMAKE_BUILD_FLAGS) $(DEBUG_ONLY_CMAKE_BUILD_FLAGS) $(PARALLEL_ONLY_CMAKE_BUILD_FLAGS)

## These can be customized via command line
## Arguments for `cmake --install <build_dir>`
CMAKE_INSTALL_FLAGS +=
ifneq ($(USER_INSTALL_DIR),)
  CMAKE_INSTALL_FLAGS += --prefix=$(USER_INSTALL_DIR)
endif

RELEASE_ONLY_CMAKE_INSTALL_FLAGS +=
DEBUG_ONLY_CMAKE_INSTALL_FLAGS +=
RELEASE_CMAKE_INSTALL_FLAGS += $(CMAKE_INSTALL_FLAGS) $(RELEASE_ONLY_CMAKE_INSTALL_FLAGS)
DEBUG_CMAKE_INSTALL_FLAGS += $(CMAKE_INSTALL_FLAGS) $(DEBUG_ONLY_CMAKE_INSTALL_FLAGS)

PARALLEL_ONLY_CMAKE_INSTALL_FLAGS +=
PARALLEL_RELEASE_CMAKE_INSTALL_FLAGS += $(CMAKE_INSTALL_FLAGS) $(RELEASE_ONLY_CMAKE_INSTALL_FLAGS) $(PARALLEL_ONLY_CMAKE_INSTALL_FLAGS)
PARALLEL_DEBUG_CMAKE_INSTALL_FLAGS += $(CMAKE_INSTALL_FLAGS) $(DEBUG_ONLY_CMAKE_INSTALL_FLAGS) $(PARALLEL_ONLY_CMAKE_INSTALL_FLAGS)

################################################################

.PHONY: default all

default: release

all: release debug parallel-release parallel-debug

################################

.PHONY: release debug
.PHONY: _dir-release _dir-debug _build-release _build-debug
## Run `cmake` unconditionally of the existence of the build dirs
## > always run all `execute_process` in CMakeLists.txt, e.g. to update `OPENSMT_GIT_DESCRIPTION`
.PHONY: $(RELEASE_BUILD_DIR) $(DEBUG_BUILD_DIR)

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

.PHONY: parallel parallel-release parallel-debug
.PHONY: _dir-parallel-release _dir-parallel-debug _build-parallel-release _build-parallel-debug
.PHONY: $(PARALLEL_RELEASE_BUILD_DIR) $(PARALLEL_DEBUG_BUILD_DIR)

parallel: parallel-release

parallel-release: _dir-parallel-release _build-parallel-release

_dir-parallel-release: $(PARALLEL_RELEASE_BUILD_DIR)

_build-parallel-release: _dir-parallel-release
	cmake --build $(PARALLEL_RELEASE_BUILD_DIR) $(PARALLEL_RELEASE_CMAKE_BUILD_FLAGS)

$(PARALLEL_RELEASE_BUILD_DIR):
	cmake -B $(PARALLEL_RELEASE_BUILD_DIR) $(PARALLEL_RELEASE_CMAKE_FLAGS)

parallel-debug: _dir-parallel-debug _build-parallel-debug

_dir-parallel-debug: $(PARALLEL_DEBUG_BUILD_DIR)

_build-parallel-debug: _dir-parallel-debug
	cmake --build $(PARALLEL_DEBUG_BUILD_DIR) $(PARALLEL_DEBUG_CMAKE_BUILD_FLAGS)

$(PARALLEL_DEBUG_BUILD_DIR):
	cmake -B $(PARALLEL_DEBUG_BUILD_DIR) $(PARALLEL_DEBUG_CMAKE_FLAGS)

################################
################################

.PHONY: test test-all

test: test-release

test-all: test-release test-debug test-parallel-release test-parallel-debug

################################

.PHONY: test-release test-debug

test-release:
	ctest --test-dir $(RELEASE_BUILD_DIR)

test-debug:
	ctest --test-dir $(DEBUG_BUILD_DIR)

################################

.PHONY: test-parallel test-parallel-release test-parallel-debug

test-parallel: test-parallel-release

test-parallel-release:
	ctest --test-dir $(PARALLEL_RELEASE_BUILD_DIR)

test-parallel-debug:
	ctest --test-dir $(PARALLEL_DEBUG_BUILD_DIR)

################################
################################

.PHONY: clean clean-all

clean: clean-release

clean-all: clean-release clean-debug clean-parallel-release clean-parallel-debug

################################

.PHONY: clean-release clean-debug

clean-release:
	rm -fr $(RELEASE_BUILD_DIR)

clean-debug:
	rm -fr $(DEBUG_BUILD_DIR)

################################

.PHONY: clean-parallel clean-parallel-release clean-parallel-debug

clean-parallel: clean-parallel-release

clean-parallel-release:
	rm -fr $(PARALLEL_RELEASE_BUILD_DIR)

clean-parallel-debug:
	rm -fr $(PARALLEL_DEBUG_BUILD_DIR)

################################
################################

.PHONY: install

install: install-release

################################

.PHONY: install-release install-debug

install-release: release
	cmake --install $(RELEASE_BUILD_DIR) $(RELEASE_CMAKE_INSTALL_FLAGS)

install-debug: debug
	cmake --install $(DEBUG_BUILD_DIR) $(DEBUG_CMAKE_INSTALL_FLAGS)

################################

.PHONY: install-parallel install-parallel-release install-parallel-debug

install-parallel: install-parallel-release

install-parallel-release: parallel-release
	cmake --install $(PARALLEL_RELEASE_BUILD_DIR) $(PARALLEL_RELEASE_CMAKE_INSTALL_FLAGS)

install-parallel-debug: parallel-debug
	cmake --install $(PARALLEL_DEBUG_BUILD_DIR) $(PARALLEL_DEBUG_CMAKE_INSTALL_FLAGS)
