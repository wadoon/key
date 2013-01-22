package de.uka.ilkd.key.smt;

import de.uni_freiburg.informatik.ultimate.smtinterpol.SMTInterface;


/**
 * Instances of this class represent autonomous invocations of the KeYnterpol
 * solver. It is not certain if it is threadsafe.
 * 
 * @author christopher
 */
public class KeYnterpolLauncher {

    public String startSession(String commands) {
        
        SMTInterface smtInterface = SMTInterface.INSTANCE;
        return smtInterface.startMessageBasedSession(commands);
    }
}
