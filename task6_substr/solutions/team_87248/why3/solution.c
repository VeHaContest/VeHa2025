#include <stdio.h>
#include <stdlib.h>

typedef struct {
    const char* s;
    int start;
    int len;
} substr_t;

substr_t make_substr(const char* s, int start, int len) {
    substr_t res;
    res.s = s;
    res.start = start;
    res.len = len;
    return res;
}

int is_digit(char c) {
    return c >= '0' && c <= '9';
}

substr_t max_left_digits(const char* s, int n) {
    int max_start = -1;
    int max_length = 0;
    int current_start = -1;
    int current_length = 0;

    for (int i = 0; i < n; i++) {
        if (is_digit(s[i])) {
            if (current_start == -1) {
                current_start = i;
                current_length = 1;
            } else {
                current_length++;
            }
        } else {
            if (current_length > max_length) {
                max_start = current_start;
                max_length = current_length;
            }
            current_start = -1;
            current_length = 0;
        }
    }

    if (current_length > max_length) {
        max_start = current_start;
        max_length = current_length;
    }

    if (max_length > 0) {
        return make_substr(s, max_start, max_length);
    } else {
        return make_substr(s, 0, 0);
    }
}

int main() {
    const char* test_str = "abc123def678";
    int n = 12;
    substr_t res = max_left_digits(test_str, n);

    printf("Longest digit substring: ");
    for (int i = 0; i < res.len; i++) {
        putchar(res.s[res.start + i]);
    }
    printf("\nLength: %d, Start: %d\n", res.len, res.start);

    return 0;
}
