package de.uka.ilkd.key.util.rifl;

import java.io.File;
import java.io.IOException;

import javax.xml.parsers.ParserConfigurationException;
import org.junit.Test;
import org.xml.sax.SAXException;

import recoder.ParserException;

public class TestRiflCLI {
	private static final File ARRAY_EXAMPLE = new File("resources/testcase/rifl/array/");
	private static final File RIFL_FILE = new File(ARRAY_EXAMPLE, "rifl.xml");
	private static final File JAVA_SOURCE = new File(ARRAY_EXAMPLE, "src/program.java");

	@Test
	public void testCli() throws ParserConfigurationException, SAXException, IOException, ParserException {
		System.out.println(ARRAY_EXAMPLE.getAbsolutePath());
		RIFLTransformer transformer = new RIFLTransformer();
		transformer.doTransform(RIFL_FILE, JAVA_SOURCE);		
	}
	
}
