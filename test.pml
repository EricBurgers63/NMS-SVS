mtype = { MESSAGE }; // Definitie van het berichttype

chan channel = [0] of { mtype }; // Kanaal met een buffer van 1 bericht

proctype Sender() {
    mtype msg = MESSAGE; // Maak een bericht aan
    printf("Zender: Verzenden van bericht...\n");
    channel!msg; // Stuur het bericht naar het kanaal
    printf("Zender: Bericht verzonden.\n");
}

proctype Receiver() {
    mtype received_msg;
    channel?received_msg; // Ontvang bericht van het kanaal
    printf("Ontvanger: Bericht ontvangen.\n");
}

init {
    run Sender();  // Start de zender
    run Receiver(); // Start de ontvanger
}
