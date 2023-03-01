#include <string.h>
#include <stdlib.h>
#include <stdio.h>

#include "memory.h"
#include "types.h"

char* type_name(char index) {
    switch (index) {
        case BOOL: return "bool";
        case INT: return "int";
        case CHAR: return "char";
        default: return "?";
    }
}

ufull_t parse_int(char* str) {
    return atoi(str);
}

byte_t parse_bool(char* str) {
    if (strcmp(str, "true") == 0) {
        return 1;
    }
    else if (strcmp(str, "false") == 0) {
        return 0;
    }
    else return -1;
}

byte_t parse_char(char* str) {
    if (str[0] == '\\') {
        if (str[2] != 0) return -1;
        switch (str[1]) {
            case 'n': return '\n';
            default: return -1;
        }
    }
    else {
        if (str[1] != 0) return -1;
        return str[0];
    }
}

byte_t* load_simple_argument(char type, char* arg) {
    switch (type) {
        case INT: {
            full_t value = parse_int(arg);
            if (value == 0 && !(strcmp(arg, "0") == 0)) { printf("Failure: expected an int, but got: %s\n", arg); return (byte_t*)-1; }
            byte_t* alloc = allocate_simple(FULL);
            *((full_t*)(alloc)) = value;
            INCR_REF_COUNT(alloc);
            return alloc;
        }
        case BOOL: {
            byte_t value = parse_bool(arg);
            if (value == -1) { printf("Failure: expected a bool, but got: %s\n", arg); return (byte_t*)-1; }
            byte_t* alloc = allocate_simple(BYTE);
            *(alloc) = value;
            INCR_REF_COUNT(alloc);
            return alloc;
        }
        case CHAR: {
            byte_t value = parse_char(arg);
            if (value == -1) { printf("Failure: expected a bool, but got: %s\n", arg); return (byte_t*)-1; }
            byte_t* alloc = allocate_simple(BYTE);
            *(alloc) = value;
            INCR_REF_COUNT(alloc);
            return alloc;
        }
        default:
            printf("Unknown simple type\n");
            return (byte_t*)-1;
    }
}