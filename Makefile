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

.PHONY: all build run clean 
