package de.tud.cs.se.ds.psec.parser.ast;

import java.util.List;

import org.objectweb.asm.MethodVisitor;

import de.tud.cs.se.ds.psec.compiler.ProgVarHelper;
import de.tud.cs.se.ds.psec.compiler.ast.RuleInstantiations;
import de.tud.cs.se.ds.psec.compiler.ast.TacletASTNode;
import de.tud.cs.se.ds.psec.util.UniqueLabelManager;
import de.uka.ilkd.key.java.Services;

/**
 * A simple {@link String} wrapper for the {@link TranslationTacletASTElement}
 * type hierarchy.
 *
 * @author Dominic Scheurer
 */
public class StringTranslationTacletASTElement
        extends TranslationTacletASTElement {

    private String str;

    public StringTranslationTacletASTElement(String str) {
        this.str = str;
    }

    public String getString() {
        return str;
    }

    @Override
    public void translate(MethodVisitor mv, ProgVarHelper pvHelper,
            UniqueLabelManager labelManager, RuleInstantiations instantiations,
            Services services, List<TacletASTNode> children) {
    }

}
