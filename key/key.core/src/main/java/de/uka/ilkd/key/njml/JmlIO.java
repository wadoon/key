package de.uka.ilkd.key.njml;

import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.speclang.PositionedString;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLConstruct;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;

/**
 * @author Alexander Weigl
 * @version 1 (7/1/20)
 */
public class JmlIO {
    private ImmutableSet<? extends PositionedString> warnings = DefaultImmutableSet.nil();

    public JmlIO(Services services, KeYJavaType containerType, ProgramVariable self, Object o, Object o1, Object o2, Object o3) {
        System.out.println("JmlIO.JmlIO");
    }

    public JmlIO() {
        System.out.println("JmlIO.JmlIO");
    }

    public ImmutableList<TextualJMLConstruct> parseClassLevel(String concatenatedComment, String fileName, Position pos) {
        System.out.println("JmlIO.parseClassLevel");
        return ImmutableSLList.nil();
    }

    public ImmutableSet<? extends PositionedString> getWarnings() {
        return warnings;
    }

    public void setWarnings(ImmutableSet<? extends PositionedString> warnings) {
        this.warnings = warnings;
    }

    public ImmutableList<TextualJMLConstruct> parseMethodlevel(String concatenatedComment, String fileName, Position position) {
        return ImmutableSLList.nil();
    }

    public Term parseExpression(PositionedString p) {
                  return null;
    }
}
