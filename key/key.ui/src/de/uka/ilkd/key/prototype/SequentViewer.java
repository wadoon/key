package de.uka.ilkd.key.prototype;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.parser.DefaultTermParser;
import de.uka.ilkd.key.parser.ParserException;
import de.uka.ilkd.key.pp.AbbrevMap;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.settings.ProofSettings;
import javafx.application.Application;
import javafx.scene.Parent;
import javafx.scene.Scene;
import javafx.scene.layout.Pane;
import javafx.scene.text.TextFlow;
import javafx.stage.Stage;

import java.io.File;
import java.io.StringReader;
import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (18.04.17)
 */
public class SequentViewer extends Application {
    @Override public void start(Stage stage) throws Exception {
        Sequent s = createTestSequent();

        Pane viewer = new SequentPane(s);
        Scene scene = new Scene(viewer, 500d, 800d);
        scene.getStylesheets().add("/style.css");
        stage.setScene(scene);
        stage.show();
    }

    private Sequent createTestSequent()
            throws ProblemLoaderException, ParserException {
        KeYEnvironment<?> env = KeYEnvironment.load(new File(
                "key.ui/src/de/uka/ilkd/key/prototype/test.key"));

        DefaultTermParser dtp = new DefaultTermParser();
        StringReader r = new StringReader(
                "a=5 ==> \\<{int i = 0;}\\>(a=5)");
       //         "(5 = a) & (15 = add(b, -3)) ==> (mul(a, b) = 90)");
        NamespaceSet nss = env.getServices().getNamespaces();
        AbbrevMap abbrev = new AbbrevMap();
        Sequent s = dtp.parseSeq(r, env.getServices(), nss, abbrev);

        System.out.println(s);

        return s;

    }

    /*private Sequent createTestSequent()
            throws ProblemLoaderException, ParserException {
        KeYEnvironment ke = KeYEnvironment.load(new File(
                "key.ui/examples/standard_key/pred_log/clam-examples/004.key"));

        DefaultTermParser dtp = new DefaultTermParser();
        StringReader r = new StringReader("\\forall int x; \\forall int j; j <= ms(x)*j\n"
                + "->\n" + "\t\\forall int a; \\forall int b; \\forall int c;\n"
                + "\t(ms(c) + ms(a)*ms(a) + ms(b)*ms(b) <\n"
                + "\t ms(c) + ms(b)*ms(b) + 2*ms(a)*ms(a)*ms(b) + ms(a)*ms(a)*ms(a)*ms(a))");
        NamespaceSet nss = new NamespaceSet();
        AbbrevMap abbrev = new AbbrevMap();
        return dtp.parseSeq(r,ke.getServices(),nss, abbrev);
    }*/
}
