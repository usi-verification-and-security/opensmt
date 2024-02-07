BUILD_DIR_BASE = build
RELEASE_BUILD_DIR = $(BUILD_DIR_BASE)
DEBUG_BUILD_DIR = $(BUILD_DIR_BASE)-debug

CMAKE_FLAGS =
RELEASE_CMAKE_FLAGS = $(CMAKE_FLAGS)
DEBUG_CMAKE_FLAGS = $(CMAKE_FLAGS) -DCMAKE_BUILD_TYPE=Debug

default: release

all: release debug

release:
	@cmake -B $(RELEASE_BUILD_DIR) $(RELEASE_CMAKE_FLAGS)
	@cmake --build $(RELEASE_BUILD_DIR)

debug:
	@cmake -B $(DEBUG_BUILD_DIR) $(DEBUG_CMAKE_FLAGS)
	@cmake --build $(DEBUG_BUILD_DIR)

clean: clean-release

clean-all: clean-release clean-debug

clean-release:
	@rm -fr $(RELEASE_BUILD_DIR)

clean-debug:
	@rm -fr $(DEBUG_BUILD_DIR)
