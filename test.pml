
proctype numberrunner() {
    int teller = 0

    do
    :: true -> {
        d_step {
            if
            ::true -> teller++;
            ::true -> teller--;
            fi
        }
        printf("%d\n", teller);
    }
    :: teller > 1000 -> break;
    :: teller < -1000 -> break;
    
    od
}

init {
    run numberrunner();  // Start de zender
}
