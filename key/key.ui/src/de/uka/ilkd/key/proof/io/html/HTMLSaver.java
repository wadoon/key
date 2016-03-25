package de.uka.ilkd.key.proof.io.html;

import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.AbstractProfile;
import de.uka.ilkd.key.proof.io.ProblemLoader;
import de.uka.ilkd.key.ui.ConsoleUserInterfaceControl;

import java.io.*;
import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.Stack;

/**
 * Saves a Proof in a proper readable format.
 * <p>
 * Created by weigl on 3/24/16.
 */
public class HTMLSaver implements Runnable {
    Proof proof;
    File saveTo;

    private PrintWriter pw;

    public HTMLSaver(Proof proof, File filename) {
        this.proof = proof;
        saveTo = filename;
    }


    /**
     * Saves the proof into the saveTo
     */
    @Override
    public void run() {
        try {
            System.out.println(saveTo.getAbsolutePath());
            pw = new PrintWriter(new BufferedWriter(new FileWriter(saveTo)));

            preamble("Test Proof"); //TODO add some useful name here
            body();
            footer();

            pw.close();
        } catch (IOException e) {
            e.printStackTrace();
        }


    }


    private void preamble(String title) {
        pw.format(getText("preamble.html"),
                title);
    }


    private void body() {
        pw.format("<h1>%s</h1>", proof.name());
        gatherInformation();

        //navigationBar();

        Node root = proof.root();
        Stack<Node> queue = new Stack<>();
        queue.add(root);

        while (!queue.isEmpty()) {
            Node node = queue.pop();
            appendNode(node);

            for (Node child : node)
                queue.push(child);
        }
    }

    private void appendNode(Node node) {
        String txt = getText("node.html");
        pw.format(txt, node.hashCode(), SequentHTMLPrinter.print(node.sequent()), navigationNodeBar(node));
    }

    private String navigationNodeBar(Node node) {
        String s = "";
        if (!node.root()) {
            int parentId = node.parent().hashCode();
            s = String.format("<a href=\"#%d\">Parent</a> |", parentId);
        }

        Optional<String> children = node.children().stream()
                .map((Node n) ->
                        String.format("<a href=\"#%d\">Child: %s</a>", node.hashCode(), node.name()))
                .reduce((a, b) -> a + " | " + b);

        if (children.isPresent())
            return s +  children.get();
        else
            return s;
    }

    private void gatherInformation() {
        Node root = proof.root();
        List<Node> queue = new ArrayList<>();
        queue.add(root);
    }


    private void footer() {
        pw.format(getText("footer.html"));
    }

    private String getText(String s) {
        try (InputStream is = getClass().getResourceAsStream(s);
             InputStreamReader reader = new InputStreamReader(is);
        ) {

            char[] buf = new char[4096];
            int len = reader.read(buf);
            return new String(buf, 0, len);
        } catch (IOException e) {
            e.printStackTrace();
            return "Could not load " + s + " due to " + e.getMessage();
        }
    }

    public static final void main(String argv[]) {
        ConsoleUserInterfaceControl control = new ConsoleUserInterfaceControl(false, true);

        File file = new File("key.ui/examples/standard_key/prop_log/contraposition.auto.proof");


        final ProblemLoader pl =
                new ProblemLoader(file, null, null, null,
                        AbstractProfile.getDefaultProfile(), false, control.getMediator(), true, null, control);
        pl.runSynchronously();

        Proof p = pl.getProof();

        System.out.println(p);

        HTMLSaver s = new HTMLSaver(p, new File("proof.html"));
        s.run();
    }

}
