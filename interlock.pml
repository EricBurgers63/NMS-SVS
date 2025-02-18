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
byte n_ovds;
byte z_ovds;


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


// Bruggen toestanden
#define B_GESPERD               0
#define B_GEEN_DOORVAART        1
#define B_AANSTONDS_DOORVAART   2
#define B_DOORVAART             3
#define B_STORING               7


inline plc( step ){
    printf("PLC: %d\n", step );
}

inline vaarrichting(richting){
    if
    ::richting == NOORD_ZUID -> printf("NZ");
    ::richting == ZUID_NOORD -> printf("ZN")
    ::else -> printf("--");
    fi

}

inline beeldovds(sein){
    if
    ::sein == GEENDOORVAART -> printf("Gx");
    ::sein == DOORVAART -> printf("GG")
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
inline rkvl() {
    printf( "(S): %d %d %d %d\t(B): %d %d %d %d %d", 
        nms_output.SluisGeenDoorvaart,
        nms_output.SluisGereedVoorDoorvaartNZ,
        nms_output.SluisGereedVoorDoorvaartZN,
        nms_output.SluisMeldstoring,
        bti_output.BrugGeenDoorvaart,
        bti_output.BrugGereedVoorDoorvaartNZ,
        bti_output.BrugGereedVoorDoorvaartZN,
        bti_output.BrugGereedVoorOnderdoorvaart,
        bti_output.BrugMeldstoring );
}



// Verificatiemodel voor Nieuwe Meersluis
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
                rkvl();
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
            printf("END \n");
            break; // voor testen, alleen 10000 plc cycles
        }
        :: else -> skip;
        fi
    }
    od
}


// verificatiemodel voor Schinkelbruggenobject
proctype Bruggen() {
    BTI_signals oir;  // output image register
    NMS_signals iir;  // input image register

    int plc_step = 0; //omdat Promela een niet-deterministische taal is, moet de volgorde van de verwerking worden geforceerd
    int count = 0;
    int opdracht_count;
    int opdracht_step;
    int mijnrichting = GEEN_RICHTING;
    int bruggentoestand = B_GESPERD;

    // PLC Cyclus
    do
    :: true -> {
        if
        :: plc_step == 0 -> {
            iir.SluisGeenDoorvaart =         nms_output.SluisGeenDoorvaart;
            iir.SluisGereedVoorDoorvaartNZ = nms_output.SluisGereedVoorDoorvaartNZ;
            iir.SluisGereedVoorDoorvaartZN = nms_output.SluisGereedVoorDoorvaartZN;
            iir.SluisMeldstoring =           nms_output.SluisMeldstoring;

        }
        :: plc_step == 1 -> {
            // Verwerking
            if
            :: bruggentoestand == B_GESPERD -> {
                nb_svs = SPER
                zb_svs = SPER
                n_ovds = GEENDOORVAART;
                z_ovds = GEENDOORVAART;
                oir.BrugGeenDoorvaart = true;          
                oir.BrugGereedVoorDoorvaartNZ = false;
                oir.BrugGereedVoorDoorvaartZN = false;
                oir.BrugGereedVoorOnderdoorvaart = false;
                oir.BrugMeldstoring = false;
                if // brug volgt de sluis
                :: ! iir.SluisGeenDoorvaart && iir.SluisGereedVoorDoorvaartNZ -> {
                    n_ovds = DOORVAART;
                    oir.BrugGeenDoorvaart = false;          
                    oir.BrugGereedVoorOnderdoorvaart = true;
                }
                :: ! iir.SluisGeenDoorvaart && iir.SluisGereedVoorDoorvaartZN -> {
                    z_ovds = DOORVAART;
                    oir.BrugGeenDoorvaart = false;          
                    oir.BrugGereedVoorOnderdoorvaart = true;
                }
                :: else -> skip;
                fi

            }
            :: bruggentoestand == B_GEEN_DOORVAART -> {
                // bij geen doorvaat is de brug bediend
                skip;
            }
            :: bruggentoestand == B_AANSTONDS_DOORVAART -> {
                // Brug is in beweging en/of wacht op vrijghave door brugwachter
                skip;
            }
            :: bruggentoestand == B_DOORVAART -> {
                // De brug is gereed voor doorvaart, en alleen als sluis doorvaart
                // toestaat zal de brug dat ook doen
                skip;
            }
            :: bruggentoestand == B_STORING -> {
                // Brug gaat is in storing
                skip;
            }
            fi

        }
        :: plc_step == 2 -> {
            bti_output.BrugGeenDoorvaart = oir.BrugGeenDoorvaart;          
            bti_output.BrugGereedVoorDoorvaartNZ = oir.BrugGereedVoorDoorvaartNZ;
            bti_output.BrugGereedVoorDoorvaartZN = oir.BrugGereedVoorDoorvaartZN;
            bti_output.BrugGereedVoorOnderdoorvaart = oir.BrugGereedVoorOnderdoorvaart;
            bti_output.BrugMeldstoring = oir.BrugMeldstoring;
        }
        :: plc_step == 3 -> {
            if // Bepaal (random) of een of meer bruggen in storing gaat
            :: true -> skip;
            :: true -> bruggentoestand = B_STORING;
            fi
            d_step {
                if
                :: bruggentoestand != B_STORING -> {
                    if
                    :: opdracht_step == 0 -> bruggentoestand = B_GEEN_DOORVAART;
                    :: opdracht_step == 1 -> {
                        if // wissel van richting
                        :: mijnrichting == NOORD_ZUID -> mijnrichting = ZUID_NOORD;
                        :: mijnrichting == ZUID_NOORD -> mijnrichting = NOORD_ZUID;
                        fi
                    }
                    :: opdracht_step == 2 -> bruggentoestand = B_AANSTONDS_DOORVAART;
                    :: opdracht_step == 3 -> bruggentoestand = B_DOORVAART;
                    :: opdracht_step == 4 -> bruggentoestand = S_GESPERD;
                    fi
                    opdracht_count++;
                    opdracht_step = opdracht_count % 5;
                }
                :: else -> skip
                fi
            }
            if // Bepaal (random) of sluis UIT storing gaat
            :: bruggentoestand == B_STORING -> skip;
            :: bruggentoestand == B_STORING -> {
                opdracht_count = 0;
                opdracht_step = opdracht_count % 7;
                bruggentoestand = S_GESPERD;
            }
            :: else -> skip;
            fi
        }
        fi

        d_step {
            count++;
            plc_step = count % 4;
        }
        count++;
        plc_step = count % 4;
        if
            :: count > 20000 -> {
                printf("END \n");
                break; // voor testen, alleen 10000 plc cycles
            }
            :: else -> skip;
        fi
    }
    od
}



init {
    run NMS();
    run Bruggen();
}