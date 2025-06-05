#include <stdio.h>
#include <stdlib.h>

// Function declaration
unsigned int mpn_add_n(unsigned int *rp, unsigned int *up, unsigned int *vp, unsigned int n);

int main(void) {
    // Define test arrays
    unsigned int a[4] = {0xFFFFFFFF, 0x00000001, 0x00000002, 0x00000003};
    unsigned int b[4] = {0x00000001, 0xFFFFFFFF, 0x00000003, 0x00000004};
    unsigned int result[4];

    // Calculate the sum using mpn_add_n
    unsigned int carry = mpn_add_n(result, a, b, 4);

    // Print the inputs
    printf("Array A: ");
    for (int i = 0; i < 4; i++) {
        printf("%08X ", a[i]);
    }
    printf("\n");

    printf("Array B: ");
    for (int i = 0; i < 4; i++) {
        printf("%08X ", b[i]);
    }
    printf("\n");

    // Print the result
    printf("Result:  ");
    for (int i = 0; i < 4; i++) {
        printf("%08X ", result[i]);
    }
    printf("\n");

    printf("Final carry: %u\n", carry);

    return 0;
}
