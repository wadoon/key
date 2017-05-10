package de.uka.ilkd.key.api;

import de.uka.ilkd.key.macros.ProofMacro;
import org.junit.Before;
import org.junit.Test;

import java.util.Collection;

import static org.junit.Assert.*;

/**
 * @author Alexander Weigl
 * @version 1 (09.05.17)
 */
public class ProofMacroApiTest {
    private ProofMacroApi mapi;

    @Before public void setUp() throws Exception {
        mapi = KeYApi.getMacroApi();
    }

    @Test public void getMacros() throws Exception {
        Collection<ProofMacro> c = mapi.getMacros();
        c.forEach(m -> System.out
                .format("%s : (%s)%n", m.getScriptCommandName(), m.getName()));
        assertTrue("Strange! No ProofMacro is defined", c.size() > 0);
    }

    @Test public void getMacro() throws Exception {
        ProofMacro ap = mapi.getMacro("autopilot");
        assertNotNull(ap);
    }

}