package edu.kit.iti.formal.psdbg.storage;

import javax.xml.bind.JAXBContext;
import javax.xml.bind.JAXBException;
import java.io.Reader;
import java.io.StringReader;
import java.io.Writer;

/**
 * @author Alexander Weigl
 * @version 1 (16.05.18)
 */
public class PersistentFacade {
    public static JAXBContext createJAXBContext() throws JAXBException {
        JAXBContext ctx = JAXBContext.newInstance(
                PersistentState.class,
                PersistentGoal.class,
                PersistentVariable.class
        );
        return ctx;
    }

    public static void write(PersistentState state, Writer output) throws JAXBException {
        JAXBContext ctx = createJAXBContext();
        ctx.createMarshaller().marshal(state, output);
    }

    public static PersistentState read(Reader file) throws JAXBException {
        JAXBContext ctx = createJAXBContext();
        return (PersistentState) ctx.createUnmarshaller().unmarshal(file);
    }
}
