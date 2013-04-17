package de.uka.ilkd.keyabs.speclang;

import antlr.RecognitionException;
import antlr.TokenStreamException;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.parser.ParserException;
import de.uka.ilkd.key.parser.ParserMode;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.AbstractEnvInput;
import de.uka.ilkd.key.proof.io.EnvInput;
import de.uka.ilkd.keyabs.abs.ABSServices;
import de.uka.ilkd.keyabs.parser.ABSKeYLexer;
import de.uka.ilkd.keyabs.parser.ABSKeYParser;
import de.uka.ilkd.keyabs.proof.init.ABSInitConfig;
import de.uka.ilkd.keyabs.speclang.dl.ABSClassInvariant;
import de.uka.ilkd.keyabs.speclang.dl.ABSClassInvariantImpl;
import de.uka.ilkd.keyabs.speclang.dl.DLSpecFactory;

import java.io.File;
import java.io.FileFilter;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.util.List;

/**
 * Created with IntelliJ IDEA.
 * User: bubel
 * Date: 28.03.13
 * Time: 17:08
 * To change this template use File | Settings | File Templates.
 */
public class ABSSLInput extends AbstractEnvInput<ABSServices, ABSInitConfig> {
    public ABSSLInput(String path, List<File> classPath, File bootClassPath) {
        super("specification", path, classPath, bootClassPath);
    }

    @Override
    public void read() throws ProofInputException {
        ABSServices services = getInitConfig().getServices();

        System.out.println("Reading class invariants");
        //services.getProgramInfo().getABSParserInfo().getClasses();
        File dir = new File(javaPath);
        File[] files = dir.listFiles(new FileFilter() {
            @Override
            public boolean accept(File pathname) {
                return pathname != null &&
                        pathname.getName().endsWith(".inv");
            }
        });

        for (File inv : files) {
            FileReader fileReader = null;
            try {
                fileReader = new FileReader(inv);
            } catch (FileNotFoundException e) {
                return;
            }
            try {
                ABSKeYParser parser
                        = new ABSKeYParser(ParserMode.TERM, new ABSKeYLexer(
                        fileReader,
                        services.getExceptionHandler()),
                        "",
                        null,
                        services,
                        services.getNamespaces());
                parser.invariants();
 /*           DLSpecFactory factory = new DLSpecFactory(services);
            LogicVariable heapVar = new LogicVariable(new Name("heapVar"),
                    services.getTypeConverter().getHeapLDT().targetSort());
            LogicVariable historyVar = new LogicVariable(new Name("historyVar"),
                    services.getTypeConverter().getHistoryLDT().targetSort());
            LogicVariable self = new LogicVariable(new Name("selfVar"), Sort.ANY);*/
            for (ABSClassInvariant classInvariant : parser.getClassInvariants()) {
                services.getSpecificationRepository().
                        addClassInvariant(classInvariant);
            }
            } catch (RecognitionException re) {
                throw new ProofInputException(re);
            } catch (TokenStreamException tse) {
                throw new ProofInputException(tse);
            }
        }

    }
}
