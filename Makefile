# Compiler settings
CC = gcc
CFLAGS = -Wall -Wextra

# Binary name
TARGET = add_strings_test.out

# Source files
SOURCES = src/add_strings.c src/add_strings_test.c

# Build and run target
all: build run

# Build the program
$(TARGET): $(SOURCES)
	$(CC) $(CFLAGS) $(SOURCES) -o $(TARGET)

build: $(TARGET)

# Run the program
run: build
	./$(TARGET)

# Clean build artifacts
clean:
	rm -f $(TARGET)

error.txt: src/bignums.c src/proofs/bignums/bignum_lemmas.v
	-command="refinedc check src/bignums.c" ./run.sh > error.txt

test: error.txt
	cat error.txt

count: error.txt
	grep -c Cannot error.txt

test_with_details: test
	./extract_error_lines.sh error.txt
	@grep -q "The call to \[dune\] returned with error code" error.txt && exit 1 || exit 0

.PHONY: all build run clean test count test_with_details
