package recoder.kit.transformation.java5to4;

import recoder.CrossReferenceServiceConfiguration;
import recoder.ProgramFactory;
import recoder.abstraction.ClassType;
import recoder.abstraction.Method;
import recoder.abstraction.Type;
import recoder.convenience.TreeWalker;
import recoder.java.Expression;
import recoder.java.NonTerminalProgramElement;
import recoder.java.ProgramElement;
import recoder.java.expression.operator.Conditional;
import recoder.java.reference.MethodReference;
import recoder.kit.ProblemReport;
import recoder.kit.TwoPassTransformation;
import recoder.kit.TypeKit;

import java.util.ArrayList;
import java.util.List;

public class MakeConditionalCompatible extends TwoPassTransformation {
    private final NonTerminalProgramElement root;

    private List<Item> list;

    public MakeConditionalCompatible(CrossReferenceServiceConfiguration sc, NonTerminalProgramElement root) {
        super(sc);
        this.root = root;
    }

    public ProblemReport analyze() {
        this.list = new ArrayList<Item>();
        setProblemReport(NO_PROBLEM);
        TreeWalker tw = new TreeWalker(this.root);
        while (tw.next()) {
            ProgramElement pe = tw.getProgramElement();
            if (pe instanceof Conditional) {
                Conditional c = (Conditional) pe;
                Type t = getSourceInfo().getType(c);
                Type e1 = getSourceInfo().getType(c.getExpressionAt(1));
                Type e2 = getSourceInfo().getType(c.getExpressionAt(2));
                if (t instanceof recoder.abstraction.IntersectionType || (e1 != e2 && (!(e1 instanceof recoder.abstraction.PrimitiveType) || !(e2 instanceof recoder.abstraction.PrimitiveType)) && e1 != getNameInfo().getNullType() && e2 != getNameInfo().getNullType() && !getSourceInfo().isWidening(e1, e2) && !getSourceInfo().isWidening(e2, e1))) {
                    Type target;
                    Expression parent = (Expression) c.getASTParent();
                    if (parent instanceof MethodReference) {
                        Method m = getSourceInfo().getMethod((MethodReference) parent);
                        ClassType classType = m.getContainingClassType();
                    } else {
                        target = getSourceInfo().getType(parent);
                    }
                    this.list.add(new Item(c, target));
                }
            }
        }
        if (this.list.isEmpty())
            return IDENTITY;
        return NO_PROBLEM;
    }

    public void transform() {
        super.transform();
        ProgramFactory f = getProgramFactory();
        for (Item i : this.list) {
            Expression e1 = i.c.getExpressionAt(1);
            Expression e2 = i.c.getExpressionAt(2);
            replace(e1, f.createTypeCast(e1.deepClone(), TypeKit.createTypeReference(f, i.t)));
            replace(e2, f.createTypeCast(e2.deepClone(), TypeKit.createTypeReference(f, i.t)));
        }
    }

    private static class Item {
        Conditional c;

        Type t;

        Item(Conditional c, Type t) {
            this.c = c;
            this.t = t;
        }
    }
}
