package keyext.extract_preconditions.projections.visitors;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.Sort;

import java.util.HashMap;

import static keyext.extract_preconditions.projections.visitors.FindVarNamesVisitor.isSelectTerm;

public class SimpleLeaveOutTermConstructionVisitor extends LeaveOutTermConstructionVisitor {
    public SimpleLeaveOutTermConstructionVisitor(TermBuilder termBuilder) {
        super(null, null, termBuilder);
    }

    @Override
    protected boolean shouldIncludeNode(Term visited) {
        if (visited.op() instanceof Junctor) {
            return true;
        }
        SimpleAdmissibleLeafFinder finder = new SimpleAdmissibleLeafFinder();
        visited.execPostOrder(finder);
        return finder.getAdmit();
    }

    private class SimpleAdmissibleLeafFinder extends FindVarNamesVisitor {

        private boolean admit = true;

        public boolean getAdmit(){
            return this.admit;
        }

        @Override
        public void visit(Term visited) {
            if (isBuiltinObjectProperty(visited)) {
                return;
            }
            if ((isSelectTerm(visited) && visited.sub(2).op().name().toString().endsWith("<created>"))
                || visited.op().name().toString().endsWith("<inv>")){
                this.admit=false;
            } else if (visited.op() instanceof Function) {
                if (visited.op().name().toString().endsWith("exactInstance")
                    || visited.op().name().toString().equals("measuredByEmpty")
                    || visited.op().name().toString().equals("wellFormed")){
                    this.admit=false;
                }
            }
        }
    }
}
