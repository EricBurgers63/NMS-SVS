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
#define GEEN_RICHTING 3

// Sluis toestanden
#define S_GESPERD               0
#define S_GEEN_DOORVAART        1
#define S_AANSTONDS_DOORVAART   2
#define S_INVAREN_TOEGESTAAN    3
#define S_INVAREN_VERBIEDEN     4
#define S_UITVAREN_TOEGESTAAN   5
#define S_UITVAREN_VERBIEDEN    6


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

    // Opstarten:
    // SYS-10731: SluisGeenDoorvaart XOR SluisGereedVoorDoorvaartNZ XOR SluisGereedVoorDoorvaartZN == TRUE
    // Aanname: Sluis start op in SPER. 

    

    // PLC Cyclus
    do
    :: true -> {
        if
        :: plc_step == 0 -> {
            atomic { // input fase
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
                    oir.SluisGeenDoorvaart = true;
                    oir.SluisGereedVoorDoorvaartNZ = false;
                    oir.SluisGereedVoorDoorvaartZN = false;
                    oir.SluisMeldstoring = false;
                    n_svs = SPER;
                    n_kolk = GEENDOORVAART;
                    z_kolk = GEENDOORVAART;
                    z_svs = SPER;
                }
                :: sluistoestand == S_GEEN_DOORVAART -> {
                    oir.SluisGeenDoorvaart = true;
                    oir.SluisGereedVoorDoorvaartNZ = false;
                    oir.SluisGereedVoorDoorvaartZN = false;
                    oir.SluisMeldstoring = false;
                    n_svs = GEENDOORVAART;
                    n_kolk = GEENDOORVAART;
                    z_kolk = GEENDOORVAART;
                    z_svs = GEENDOORVAART;
                }
                :: sluistoestand == S_AANSTONDS_DOORVAART -> {
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
                :: sluistoestand == S_INVAREN_TOEGESTAAN -> {
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
                :: sluistoestand == S_INVAREN_VERBIEDEN -> {
                    oir.SluisGeenDoorvaart = true;
                    oir.SluisGereedVoorDoorvaartNZ = false;
                    oir.SluisGereedVoorDoorvaartZN = false;
                    oir.SluisMeldstoring = false;
                    n_svs = GEENDOORVAART;
                    n_kolk = GEENDOORVAART;
                    z_kolk = GEENDOORVAART;
                    z_svs = GEENDOORVAART;
                }
                :: sluistoestand == S_UITVAREN_TOEGESTAAN -> {
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
                :: sluistoestand == S_UITVAREN_VERBIEDEN -> {
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
                    :: mijnrichting = ZUID_NOORD -> n_kolk = GEENDOORVAART;
                    :: else -> skip;
                    fi
                }
            fi
        }
        :: plc_step == 2 -> {
            atomic { // output fase
                nms_output.SluisGeenDoorvaart =         oir.SluisGeenDoorvaart;
                nms_output.SluisGereedVoorDoorvaartNZ = oir.SluisGereedVoorDoorvaartNZ;
                nms_output.SluisGereedVoorDoorvaartZN = oir.SluisGereedVoorDoorvaartZN;
                nms_output.SluisMeldstoring =           oir.SluisMeldstoring;
            }
        }
        :: plc_step == 3 -> { // Huishouding
            if
            :: opdracht_step == 0 ->{
                if // kies een (random) richting
                :: true -> mijnrichting = NOORD_ZUID;
                :: true -> mijnrichting = ZUID_NOORD;
                fi
            }
            :: opdracht_step == 1 -> sluistoestand = S_INVAREN_TOEGESTAAN;
            :: opdracht_step == 2 -> sluistoestand = S_INVAREN_VERBIEDEN;
            :: opdracht_step == 3 -> sluistoestand = S_UITVAREN_TOEGESTAAN;
            :: opdracht_step == 4 -> sluistoestand = S_UITVAREN_VERBIEDEN;
            :: opdracht_step == 5 -> sluistoestand = S_GEEN_DOORVAART;
            fi
            // selectie voor de volgende opdracht
            opdracht_count++;
            opdracht_step = opdracht_count % 6;
        }
        fi

        atomic {
            count++;
            plc_step = count % 4;
        }
        if
        :: count > 10000 -> {
            printf("END\n")
            break; // voor testen, alleen 10000 plc cycles
        }
        :: else -> skip;
        fi
    }
    od
}


// verificatiemodel voor SVS subsysteem
proctype SVS() {
    
}

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
