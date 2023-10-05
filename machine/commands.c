#include <string.h>
#include <stdio.h>

#include "commands.h"
#include "memory.h"

byte_t command_index(char* command) {
    if (strcmp(command, "i") == 0) return I;
    else if (strcmp(command, "disass") == 0) return DISASS;
    else if (strcmp(command, "run") == 0) return RUN;
    else if (strcmp(command, "comp") == 0) return COMPILE;
    else if (strcmp(command, "help") == 0) return HELP;
    else return -1;
}

byte_t is_flag(char* flag) {
    if (flag[0] == '-' && flag[1] == '-') return true;
    else return false;
}

byte_t flag_index(char* flag) {
    if (strcmp(flag, "--trace") == 0) return TRACE;
    else if (strcmp(flag, "--time") == 0) return TIME;
    else return -1;
}