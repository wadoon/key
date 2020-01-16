package de.uka.ilkd.key.solidity;

import java.io.File;
import java.io.IOException;
import java.net.MalformedURLException;
import java.net.URI;

import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;

import de.uka.ilkd.key.parser.solidity.SolidityLexer;
import de.uka.ilkd.key.parser.solidity.SolidityParser;
import de.uka.ilkd.key.parser.solidity.SolidityParser.SourceUnitContext;
import de.uka.ilkd.key.parser.solidity.SolidityTranslationVisitor;

public class Solidity2KeY {
	
	private URI solidityLocation;
	
	public Solidity2KeY(File f) {
		solidityLocation = f.toURI();		
	}
	
	public Solidity2KeY(String f) {
		this(new File(f));
	}

	
	public String translate() throws MalformedURLException, IOException {
		SolidityLexer lexer = new SolidityLexer(CharStreams.fromStream(solidityLocation.toURL().openStream()));
		SolidityParser parser = new SolidityParser(new CommonTokenStream(lexer));
		SolidityTranslationVisitor visitor = new SolidityTranslationVisitor();
		SourceUnitContext solidityAST = parser.sourceUnit();
		visitor.visit(solidityAST);
		return visitor.getOutput();
	}
	
	public static void main(String[] args) {
		Solidity2KeY s = 
				new Solidity2KeY("/Users/bubel/Documents/Work/Development Projects/coreKeY/key/key/key.ui/examples/solidity/sol/auction-single-simple.sol"); 
				//new Solidity2KeY("/Users/bubel/Documents/Work/Development Projects/coreKeY/key/key/key.core/src/main/java/de/uka/ilkd/key/solidity/contract-single-player-pre-post.sol");
		try {
			System.out.println(s.translate());
		} catch (IOException e) {
			e.printStackTrace();
		}
	}

	
	
}
