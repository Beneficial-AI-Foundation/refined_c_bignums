#include <stdlib.h>
#include <stdio.h>

char* add_binary_strings(const char*, const char*);

int main() {
    const char* a = "1011";  // Same binary number as before
    const char* b = "1101";  // Same binary number as before

    char* sum = add_binary_strings(a, b);
    printf("%s + %s = %s\n", a, b, sum);

    free(sum);  // Don't forget to free the allocated memory
    return 0;
}
