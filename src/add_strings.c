//#include <stdio.h>
#include <stdlib.h>
#include <string.h>

// TODO Remove magic numbers
// Verifies the string contains only '0' and '1' characters
int is_valid_bit_string(const char* s) {
    while (*s) {
        if (*s != 48 && *s != 49) return 0;
        s++;
    }
    return 1;
}

// Removes leading zeros and ensures empty strings become "0"
char* normalize_bit_string(const char* s) {
    // Skip leading zeros
    while (*s == 48 && *(s+1) != 0) {
        s++;
    }

    // Allocate and copy the normalized string
    char* result = strdup(s);
    return result;
}

char* add_binary_strings(const char* s1, const char* s2) {
    // Validate inputs
    if (!is_valid_bit_string(s1) || !is_valid_bit_string(s2)) {
        return NULL;
    }

    // Normalize inputs
    char* x = normalize_bit_string(s1);
    char* y = normalize_bit_string(s2);

    // Special case: if y is "0", return x
    if (y[0] == 48 && y[1] == 0) {
        free(y);
        return x;
    }

    int len1 = strlen(x);
    int len2 = strlen(y);
    int max_len = (len1 > len2 ? len1 : len2) + 1; // +1 for potential carry

    // Allocate result buffer (reversed order initially)
    char* temp = malloc(max_len + 1); // +1 for null terminator
    temp[max_len] = 0;

    int carry = 0;
    int i = len1 - 1;  // index for x (rightmost digit)
    int j = len2 - 1;  // index for y (rightmost digit)
    int k = max_len - 1;  // index for result (rightmost position)

    // Perform addition right-to-left (least significant bit first)
    while (i >= 0 || j >= 0 || carry > 0) {
        int bit_x = (i >= 0) ? (x[i] - 48) : 0;
        int bit_y = (j >= 0) ? (y[j] - 48) : 0;

        int sum = bit_x + bit_y + carry;
        temp[k] = (sum % 2) + 48;  // Current bit is sum modulo 2
        carry = sum / 2;            // Carry is integer division by 2

        i--; j--; k--;
    }

    // Free the normalized inputs
    free(x);
    free(y);

    // If we didn't use the entire buffer, shift result left
    char* result;
    if (k < 0) {
        // Used the entire buffer
        result = temp;
    } else {
        // Need to normalize
        result = strdup(temp + k + 1);
        free(temp);
    }

    return result;
}

// Example usage
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
    //printf("%s + %s = %s\n", a, b, sum);

    free(sum);  // Don't forget to free the allocated memory
    return 0;
}
