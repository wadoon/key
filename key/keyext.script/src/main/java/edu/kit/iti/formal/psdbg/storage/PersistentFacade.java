package edu.kit.iti.formal.psdbg.storage;

import com.fasterxml.jackson.databind.ObjectMapper;
import com.fasterxml.jackson.databind.SerializationFeature;

import java.io.IOException;
import java.io.Reader;
import java.io.Writer;

/**
 * @author Alexander Weigl
 * @version 1 (16.05.18)
 */
public class PersistentFacade {
    public static ObjectMapper createJAXBContext() {
        ObjectMapper mapper = new ObjectMapper();
        mapper.enable(SerializationFeature.INDENT_OUTPUT);
        mapper.disable(SerializationFeature.WRITE_DATES_AS_TIMESTAMPS);
        return mapper;
    }

    public static void write(PersistentState state, Writer output) throws IOException {
        createJAXBContext().writer().writeValue(output, state);
    }

    public static PersistentState read(Reader file) throws IOException {
        return createJAXBContext().readValue(file, PersistentState.class);
    }
}
