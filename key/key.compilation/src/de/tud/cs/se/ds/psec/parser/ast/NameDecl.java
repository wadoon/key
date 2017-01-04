package de.tud.cs.se.ds.psec.parser.ast;

import java.util.List;

import org.objectweb.asm.MethodVisitor;

import de.tud.cs.se.ds.psec.compiler.ProgVarHelper;
import de.tud.cs.se.ds.psec.compiler.ast.RuleInstantiations;
import de.tud.cs.se.ds.psec.compiler.ast.TacletASTNode;
import de.tud.cs.se.ds.psec.util.UniqueLabelManager;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Named;

/**
 * A special construct for creating names from location variables, with an
 * explicit suffix.
 *
 * @author Dominic Scheurer
 */
public class NameDecl extends TranslationTacletASTElement {

    private String locVarSV, extension;

    public NameDecl(String locVarSV, String extension) {
        this.locVarSV = locVarSV;
        this.extension = extension;
    }

    public String getName(RuleInstantiations instantiations) {
        return ((Named) instantiations.getInstantiationFor(locVarSV).get())
                .name().toString() + extension;
    }

    @Override
    public void translate(MethodVisitor mv, ProgVarHelper pvHelper,
            UniqueLabelManager labelManager, RuleInstantiations instantiations,
            Services services, List<TacletASTNode> children) {
        // This element should not be translated.
        // That's maybe a design flaw...
    }

}
