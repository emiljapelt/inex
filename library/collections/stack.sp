struct stack<T>(top: T, rest: stack<T>);

external push<T>(elem: T, stck: stack<T>) {
    stck := {elem, stck};
}

external peek<T>(stck: stack<T>, out: T) {
    out := stck.top;
}

external pop<T>(stck: stack<T>, out: T) {
    out := stck.top;
    stck := stck.rest;
}

external size<T>(stck: const stack<T>, out: int) {
    pointer :stable:= $stck;
    out := 0;
    until(pointer = null) {
        out +:= 1;
        pointer := pointer.rest;
    }
}

external from_array<T>(a: T[], out: stack<T>) {
    out := null;
    for(i ::= 0; i < |a|; i +:= 1) 
        out := {a[i], out};
}