//
// Created by Matteo Marescotti on 02/12/15.
//

#include "Settings.h"


Settings Settings::Default = Settings();

Settings &Settings::Load(int argc, char **argv) {
    //int c;
    Settings *settings = new Settings();
    /*while ((c = getopt (argc, argv, "")) != -1)
        switch (c)
        {
            case 'a':
                aflag = 1;
                break;
            case 'b':
                bflag = 1;
                break;
            case 'c':
                cvalue = optarg;
                break;
            case '?':
                if (optopt == 'c')
                    fprintf (stderr, "Option -%c requires an argument.\n", optopt);
                else if (isprint (optopt))
                    fprintf (stderr, "Unknown option `-%c'.\n", optopt);
                else
                    fprintf (stderr,
                             "Unknown option character `\\x%x'.\n",
                             optopt);
                return 1;
            default:
                abort ();
        }*/

    return *settings;
}
