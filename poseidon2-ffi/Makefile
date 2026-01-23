# Makefile for building the Poseidon2 FFI library for Lean
#
# This builds a shared library that can be loaded by Lean4 via FFI.
# The library combines the Rust Poseidon2 implementation with a C shim
# that interfaces with Lean's object system.

# Detect OS for library extension
UNAME_S := $(shell uname -s)
ifeq ($(UNAME_S),Darwin)
    LIB_EXT := dylib
    SHARED_FLAG := -dynamiclib
else
    LIB_EXT := so
    SHARED_FLAG := -shared
endif

# Paths
RUST_TARGET_DIR := ../target/release
RUST_STATIC_LIB := $(RUST_TARGET_DIR)/libposeidon2_ffi.a
OUTPUT_LIB := libposeidon2_ffi_lean.$(LIB_EXT)

# Find Lean include path - try common locations
LEAN_INCLUDE := $(shell lean --print-prefix 2>/dev/null)/include
ifeq ($(wildcard $(LEAN_INCLUDE)/lean/lean.h),)
    # Try elan toolchain path
    LEAN_INCLUDE := $(HOME)/.elan/toolchains/leanprover-lean4-v4.12.0/include
endif

# Compiler flags
CC := gcc
CFLAGS := -fPIC -O2 -I$(LEAN_INCLUDE)
LDFLAGS := $(SHARED_FLAG) -L$(RUST_TARGET_DIR)

.PHONY: all clean rust

all: $(OUTPUT_LIB)

# Build Rust library
rust:
	cd .. && cargo build --release -p poseidon2-ffi

$(RUST_STATIC_LIB): rust

# Build the combined shared library
$(OUTPUT_LIB): src/lean_shim.c $(RUST_STATIC_LIB)
	$(CC) $(CFLAGS) $(LDFLAGS) -o $@ $< \
		-Wl,--whole-archive $(RUST_STATIC_LIB) -Wl,--no-whole-archive \
		-lpthread -ldl -lm

# macOS version (different linker flags)
ifeq ($(UNAME_S),Darwin)
$(OUTPUT_LIB): src/lean_shim.c $(RUST_STATIC_LIB)
	$(CC) $(CFLAGS) $(SHARED_FLAG) -o $@ $< \
		-Wl,-force_load,$(RUST_STATIC_LIB) \
		-lpthread -ldl -lm
endif

clean:
	rm -f $(OUTPUT_LIB)
	rm -f *.o

# Install to feature-B directory
install: $(OUTPUT_LIB)
	cp $(OUTPUT_LIB) ../../feature-B/

.PHONY: install
