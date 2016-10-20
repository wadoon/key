package de.tud.cs.se.ds.psec.parser.ast;

import java.util.List;

import org.objectweb.asm.MethodVisitor;

import de.tud.cs.se.ds.psec.compiler.ProgVarHelper;
import de.tud.cs.se.ds.psec.compiler.ast.RuleInstantiations;
import de.tud.cs.se.ds.psec.compiler.ast.TacletASTNode;
import de.tud.cs.se.ds.psec.util.UniqueLabelManager;
import de.uka.ilkd.key.java.Services;

/**
 * Request for the translation of the children in the taclet AST.
 *
 * @author Dominic Scheurer
 */
public class ChildCall extends Instruction {

    private int childNo;

    /**
     * Constructs a new {@link ChildCall} to the child in the taclet AST with
     * the given number.
     * 
     * @param childNo
     *            The numer of the child to be compiled.
     */
    public ChildCall(int childNo) {
        this.childNo = childNo;
    }

    /**
     * @return The index of the child to be called; lowest index is 1 (not 0)!
     */
    public int getChildNo() {
        return childNo;
    }

    @Override
    public void translate(MethodVisitor mv, ProgVarHelper pvHelper,
            UniqueLabelManager labelManager, RuleInstantiations instantiations,
            Services services, List<TacletASTNode> children) {
        // XXX Remove this hack!!! Test cases: testSimpleWhile, testSimpleFor
        // Applies in loop transformation: The body has a last statement that
        // expects a child, but has none. The real child is part of the loop
        // compilation...
        if (children.size() > childNo - 1) {
            children.get(childNo - 1).compile();
        }
    }

}
