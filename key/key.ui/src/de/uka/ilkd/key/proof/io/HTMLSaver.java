package de.uka.ilkd.key.proof.io;

import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;

import java.io.*;
import java.util.ArrayList;
import java.util.List;
import java.util.Stack;

/**
 * Saves a Proof in a proper readable format.
 * <p>
 * Created by weigl on 3/24/16.
 */
public class HTMLSaver extends Runnable {
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

        while(!queue.isEmpty()) {
            Node node = queue.pop();
            appendNode(node);


        }
    }

    private void appendNode(Node node) {
        String txt = getText("node.html");
        pw.format(
                txt, node.hashCode(), node.sequent()
        );
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
        ProofSaver

    }

}
