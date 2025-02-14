// RKVL-0688 signalen
// dit zijn de definities van de (logische) representaties van de actuele waarden 
// de op bedrading tussen de STI en de BTI.
typedef NMS_signals {
    bit SluisGeenDoorvaart;
    bit SluisGereedVoorDoorvaartNZ;
    bit SluisGereedVoorDoorvaartZN;
    bit SluisMeldstoring;
}

typedef BTI_signals {
    bit BrugGeenDoorvaart;
    bit BrugGereedVoorDoorvaartNZ;
    bit BrugGereedVoorDoorvaartZN;
    bit BrugGereedVoorOnderdoorvaart;
    bit BrugMeldstoring;
}

// RKVL-0668 
// instantiatie van de interlock
NMS_signals nms_output;
BTI_signals bti_output;


// Toestanden van de seinen
#define SPER                1
#define GEENDOORVAART       2
#define AANSTONDSDOORVAART  4
#define DOORVAART           8

// De seinen van de sluis, vereenvoudigd
byte z_svs;
byte n_svs;
byte n_kolk;
byte z_kolk;

// De seinen van de Brug, vereenvoudigd
byte nb_svs;
byte zb_svs;



// Richtingen waarin een schutting/draai kan plaastvinden
#define NOORD_ZUID 1
#define ZUID_NOORD 2
#define GEEN_RICHTING 0

// Sluis toestanden
#define S_GESPERD               0
#define S_GEEN_DOORVAART        1
#define S_AANSTONDS_DOORVAART   2
#define S_INVAREN_TOEGESTAAN    3
#define S_INVAREN_VERBIEDEN     4
#define S_UITVAREN_TOEGESTAAN   5
#define S_UITVAREN_VERBIEDEN    6
#define S_STORING               7


inline vaarrichting(richting){
    if
    ::richting == NOORD_ZUID -> printf("NZ");
    ::richting == ZUID_NOORD -> printf("ZN")
    ::else -> printf("--");
    fi

}

inline beeldk(sein){
    if
    ::sein == GEENDOORVAART -> printf("Rx");
    ::sein == DOORVAART -> printf("xG")
    ::else -> printf("--");
    fi
}

inline beeld(sein){
    if
    ::sein == SPER -> printf("RxR");
    ::sein == GEENDOORVAART -> printf("Rxx");
    ::sein == AANSTONDSDOORVAART -> printf("RGx");
    ::sein == DOORVAART -> printf("xGx");
    ::else -> printf("---");
    fi
}

inline seinbeelden() {
    beeld(n_svs);
    beeldk(n_kolk);
    beeldk(z_kolk);
    beeld(nb_svs);
    beeld(z_svs);
    beeld(zb_svs);
}

inline storing(status) {
    if
    :: status == S_STORING -> printf("S");
    :: status != S_STORING -> printf(" ");
    fi
}

// helper functie om de status van seinen en interlock te presenteren
// de seinen worden gepresenteerd in de volgorde van nood naar zuid, per 
// nautisch object.
inline status() {
    printf( "RKVL(S): %d %d %d %d\tRKVL(B): %d %d %d %d %d\tSVS(B): %d %d\tSVS(S) %d %d %d %d\n", 
        nms_output.SluisGeenDoorvaart,
        nms_output.SluisGereedVoorDoorvaartNZ,
        nms_output.SluisGereedVoorDoorvaartZN,
        nms_output.SluisMeldstoring,
        bti_output.BrugGeenDoorvaart,
        bti_output.BrugGereedVoorDoorvaartNZ,
        bti_output.BrugGereedVoorDoorvaartZN,
        bti_output.BrugGereedVoorOnderdoorvaart,
        bti_output.BrugMeldstoring,
        nb_svs, zb_svs, n_svs, n_kolk, z_kolk,  z_svs
        );
}



// Verificatiemodel voor Sluis subsysteem
proctype NMS() {
    BTI_signals iir;  // input image register
    NMS_signals oir;  // output image register

    int plc_step = 0; //omdat Promela een niet-deterministische taal is, moet de volgorde van de verwerking worden geforceerd
    int count = 0;
    int opdracht_count;
    int opdracht_step;
    int mijnrichting = GEEN_RICHTING;
    int sluistoestand = S_GESPERD;

    if // kies een (random) richting
    :: true -> {
        mijnrichting = ZUID_NOORD;
    }
    :: true -> {
        mijnrichting = NOORD_ZUID;
    }   
    fi

    // PLC Cyclus
    do
    :: true -> {
        if
        :: plc_step == 0 -> {
            d_step {
                iir.BrugGeenDoorvaart =             bti_output.BrugGeenDoorvaart;
                iir.BrugGereedVoorDoorvaartNZ =     bti_output.BrugGereedVoorDoorvaartNZ;
                iir.BrugGereedVoorDoorvaartZN =     bti_output.BrugGereedVoorDoorvaartZN;
                iir.BrugGereedVoorOnderdoorvaart =  bti_output.BrugGereedVoorOnderdoorvaart;
                iir.BrugMeldstoring =               bti_output.BrugMeldstoring;
            }
        }
        :: plc_step == 1 -> { // Verwerkingsfase
            if
                :: sluistoestand == S_GESPERD -> {
                    d_step {
                        oir.SluisGeenDoorvaart = true;
                        oir.SluisGereedVoorDoorvaartNZ = false;
                        oir.SluisGereedVoorDoorvaartZN = false;
                        oir.SluisMeldstoring = false;
                        n_svs = SPER;
                        n_kolk = GEENDOORVAART;
                        z_kolk = GEENDOORVAART;
                        z_svs = SPER;
                    }
                }
                :: sluistoestand == S_GEEN_DOORVAART -> {
                    d_step {
                        oir.SluisGeenDoorvaart = true;
                        oir.SluisGereedVoorDoorvaartNZ = false;
                        oir.SluisGereedVoorDoorvaartZN = false;
                        oir.SluisMeldstoring = false;
                        n_svs = GEENDOORVAART;
                        n_kolk = GEENDOORVAART;
                        z_kolk = GEENDOORVAART;
                        z_svs = GEENDOORVAART;
                    }
                }
                :: sluistoestand == S_AANSTONDS_DOORVAART -> {
                    d_step {
                        oir.SluisGeenDoorvaart = true;
                        oir.SluisGereedVoorDoorvaartNZ = false;
                        oir.SluisGereedVoorDoorvaartZN = false;
                        oir.SluisMeldstoring = false;
                        n_svs = GEENDOORVAART;
                        n_kolk = GEENDOORVAART;
                        z_kolk = GEENDOORVAART;
                        z_svs = GEENDOORVAART;
                        if
                        :: mijnrichting == NOORD_ZUID -> n_svs = AANSTONDSDOORVAART;
                        :: mijnrichting == ZUID_NOORD -> z_svs = AANSTONDSDOORVAART;
                        :: else -> skip;
                        fi
                    }
                }
                :: sluistoestand == S_INVAREN_TOEGESTAAN -> {
                    d_step {
                        oir.SluisGeenDoorvaart = true;
                        oir.SluisGereedVoorDoorvaartNZ = false;
                        oir.SluisGereedVoorDoorvaartZN = false;
                        oir.SluisMeldstoring = false;
                        n_svs = GEENDOORVAART;
                        n_kolk = GEENDOORVAART;
                        z_kolk = GEENDOORVAART;
                        z_svs = GEENDOORVAART;
                        if
                        :: mijnrichting == NOORD_ZUID -> n_svs = DOORVAART;
                        :: mijnrichting ==  ZUID_NOORD -> {
                            z_svs = DOORVAART;
                            oir.SluisGereedVoorDoorvaartZN = true;
                            oir.SluisGeenDoorvaart = false;
                        }
                        :: else -> skip;
                        fi
                    }
                }
                :: sluistoestand == S_INVAREN_VERBIEDEN -> {
                    d_step {
                        oir.SluisGeenDoorvaart = true;
                        oir.SluisGereedVoorDoorvaartNZ = false;
                        oir.SluisGereedVoorDoorvaartZN = false;
                        oir.SluisMeldstoring = false;
                        n_svs = GEENDOORVAART;
                        n_kolk = GEENDOORVAART;
                        z_kolk = GEENDOORVAART;
                        z_svs = GEENDOORVAART;
                    }
                }
                :: sluistoestand == S_UITVAREN_TOEGESTAAN -> {
                    d_step {
                        oir.SluisGeenDoorvaart = true;
                        oir.SluisGereedVoorDoorvaartNZ = false;
                        oir.SluisGereedVoorDoorvaartZN = false;
                        oir.SluisMeldstoring = false;
                        n_svs = GEENDOORVAART;
                        n_kolk = GEENDOORVAART;
                        z_kolk = GEENDOORVAART;
                        z_svs = GEENDOORVAART;
                        if
                        :: mijnrichting ==  NOORD_ZUID -> {
                            z_kolk = DOORVAART;
                            oir.SluisGereedVoorDoorvaartNZ = true;
                            oir.SluisGeenDoorvaart = false;
                        }
                        :: mijnrichting == ZUID_NOORD -> n_kolk = DOORVAART;
                        :: else -> skip;
                        fi
                    }
                }
                :: sluistoestand == S_UITVAREN_VERBIEDEN -> {
                    d_step {
                        oir.SluisGeenDoorvaart = true;
                        oir.SluisGereedVoorDoorvaartNZ = false;
                        oir.SluisGereedVoorDoorvaartZN = false;
                        oir.SluisMeldstoring = false;
                        n_svs = GEENDOORVAART;
                        n_kolk = GEENDOORVAART;
                        z_kolk = GEENDOORVAART;
                        z_svs = GEENDOORVAART;
                        if
                        :: mijnrichting == NOORD_ZUID -> z_kolk = GEENDOORVAART;
                        :: mijnrichting == ZUID_NOORD -> n_kolk = GEENDOORVAART;
                        :: else -> skip;
                        fi
                    }
                }
                :: sluistoestand == S_STORING -> {
                    d_step {
                        oir.SluisGeenDoorvaart = false;
                        oir.SluisGereedVoorDoorvaartNZ = false;
                        oir.SluisGereedVoorDoorvaartZN = false;
                        oir.SluisMeldstoring = true;
                        n_svs = SPER;
                        n_kolk = GEENDOORVAART;
                        z_kolk = GEENDOORVAART;
                        z_svs = SPER;
                    }
                }

            fi
        }
        :: plc_step == 2 -> {
            d_step { // output fase
                nms_output.SluisGeenDoorvaart =         oir.SluisGeenDoorvaart;
                nms_output.SluisGereedVoorDoorvaartNZ = oir.SluisGereedVoorDoorvaartNZ;
                nms_output.SluisGereedVoorDoorvaartZN = oir.SluisGereedVoorDoorvaartZN;
                nms_output.SluisMeldstoring =           oir.SluisMeldstoring;
                storing(sluistoestand);
                vaarrichting(mijnrichting);
                seinbeelden();
                printf("\n");
            }
        }
        :: plc_step == 3 -> { // Huishouding
            if // Bepaal (random) of sluis in storing gaat
            :: true -> skip;
            :: true -> sluistoestand = S_STORING;
            fi
            d_step {
                if
                :: sluistoestand != S_STORING -> {
                    if
                    :: opdracht_step == 0 -> {
                        if // wissel van richting
                        :: mijnrichting == NOORD_ZUID -> mijnrichting = ZUID_NOORD;
                        :: mijnrichting == ZUID_NOORD -> mijnrichting = NOORD_ZUID;
                        fi
                    }
                    :: opdracht_step == 1 -> sluistoestand = S_INVAREN_VERBIEDEN;
                    :: opdracht_step == 2 -> sluistoestand = S_INVAREN_TOEGESTAAN;
                    :: opdracht_step == 3 -> sluistoestand = S_INVAREN_VERBIEDEN;
                    :: opdracht_step == 4 -> sluistoestand = S_UITVAREN_TOEGESTAAN;
                    :: opdracht_step == 5 -> sluistoestand = S_UITVAREN_VERBIEDEN;
                    :: opdracht_step == 6 -> sluistoestand = S_GEEN_DOORVAART;
                    // :: opdracht_step == 7 -> sluistoestand = S_GESPERD;
                    fi
                    opdracht_count++;
                    opdracht_step = opdracht_count % 7;
                }
                :: else -> skip
                fi
            }
            if // Bepaal (random) of sluis UIT storing gaat
            :: sluistoestand == S_STORING -> skip;
            :: sluistoestand == S_STORING -> {
                opdracht_count = 0;
                opdracht_step = opdracht_count % 7;
                sluistoestand = S_GESPERD;
            }
            :: else -> skip;
            fi
        }
        fi

        d_step {
            count++;
            plc_step = count % 4;
        }
        if
        :: count > 20000 -> {
            printf("END \n")
            break; // voor testen, alleen 10000 plc cycles
        }
        :: else -> skip;
        fi
    }
    od
}


// verificatiemodel voor SVS subsysteem

init {
    atomic {
        nms_output.SluisGeenDoorvaart = false;
        nms_output.SluisGereedVoorDoorvaartNZ = false;
        nms_output.SluisGereedVoorDoorvaartZN = false;
        nms_output.SluisMeldstoring = false;
    }
    run NMS();
    // run SVS();
}