package de.uka.ilkd.key.proof.runallproofs;

import java.io.File;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Queue;

import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.util.Pair;

public class StatisticsGathering  {

    private final Proof proof;
    private final File file;

    public StatisticsGathering(Proof proof, File keyFile) {
        this.proof = proof;
        this.file = new File(keyFile.getAbsolutePath() + ".data");
    }

    public void save() throws IOException {
        try(PrintWriter pw = new PrintWriter(file)) {

            Queue<Pair<Node, Integer>> nodes = new LinkedList<>();
            nodes.add(new Pair<Node, Integer>(proof.root(), 0));

            while(!nodes.isEmpty()) {
                Pair<Node,Integer> entry = nodes.remove();
                Node n = entry.first;
                int depth = entry.second;
                int astSize = countAST(n);

                pw.printf("%d, %d, %d%n", n.serialNr(), depth, astSize);

                depth++;
                Iterator<Node> it = n.childrenIterator();
                while(it.hasNext()) {
                    Node child = it.next();
                    nodes.add(new Pair<Node, Integer>(child, depth));
                }
            }

        }
    }

    public static int countAST(Node n) {
        return countAST(n.sequent());
    }

    private static int countAST(Sequent sequent) {
        int sum = 0;
        for(SequentFormula f : sequent.antecedent().asList()) {
            sum += countAST(f.formula());
        }
        for(SequentFormula f : sequent.succedent().asList()) {
            sum += countAST(f.formula());
        }
        return sum;
    }

    private static int countAST(Term term) {
        int sum = 0;
        for(Term t : term.subs()) {
            sum += countAST(t);
        }
        return sum + 1;
    }


}
