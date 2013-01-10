package de.uka.ilkd.key.testgeneration.cli;

import com.beust.jcommander.Parameter;

/**
 * Provides a CLI interface for KeYTestGen2
 * 
 * @author christopher
 */
public final class KTGCommandLineInterface {

    @Parameter
    private boolean debug;
    
    private static void printAbout() {

        System.out.println("\nKeYTestGen2 version 0.1 \n\n"
                + "KeYTestGen2 is part of the KeY project, a system for integrated, deductive\n"
                + "software design. For more info, please visit: www.key-project.org\n\n"
                + "Copyright (C) 2012  Christopher Svanefalk\n"
                + "This is free software, and you are welcome to redistribute it, under the\n"
                + "terms of the GNU General Public License, version 2.0 or later. See the\n"
                + "GPL for more details\n\n"
                + "This software is distributed in the hope that it will be (very!) useful,\n"
                + "however, WITHOUT ANY WARRANTIES WHATSOEVER. Please see the GPL\n"
                + "for a full disclaimer");
    }
}