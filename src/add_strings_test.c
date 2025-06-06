#include <stdlib.h>
#include <stdio.h>

char* add_binary_strings(const char*, const char*);

int main() {
    char a[5];  // Need 5 characters including null terminator
    a[0] = 49;  // ASCII for digit 1
    a[1] = 48;  // ASCII for digit 0
    a[2] = 49;  // ASCII for digit 1
    a[3] = 49;  // ASCII for digit 1
    a[4] = 0;   // null terminator

    char b[5];  // Need 5 characters including null terminator
    b[0] = 49;  // ASCII for digit 1
    b[1] = 49;  // ASCII for digit 1
    b[2] = 48;  // ASCII for digit 0
    b[3] = 49;  // ASCII for digit 1
    b[4] = 0;   // null terminator

    char* sum = add_binary_strings(a, b);
    printf("%s + %s = %s\n", a, b, sum);

    free(sum);  // Don't forget to free the allocated memory
    return 0;
}
