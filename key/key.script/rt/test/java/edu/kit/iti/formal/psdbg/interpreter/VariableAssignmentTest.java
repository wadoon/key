package edu.kit.iti.formal.psdbg.interpreter;

import edu.kit.iti.formal.psdbg.interpreter.data.VariableAssignment;
import edu.kit.iti.formal.psdbg.parser.data.Value;
import edu.kit.iti.formal.psdbg.parser.types.SimpleType;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

/**
 * Created by sarah on 5/23/17.
 */
public class VariableAssignmentTest {
    VariableAssignment va1;
    VariableAssignment va2;
    VariableAssignment va3;

    @Before
    public void setup() {
        va1 = new VariableAssignment(null);
        va1.declare("a", SimpleType.INT);
        va1.declare("b", SimpleType.INT);
        va1.declare("c", SimpleType.INT);
        va1.assign("a", Value.from(1));
        va1.assign("b", Value.from(2));
        va1.assign("c", Value.from(3));

        va2 = new VariableAssignment(null);
        va2.declare("d", SimpleType.INT);
        va2.declare("e", SimpleType.INT);
        va2.declare("f", SimpleType.INT);
        va2.assign("d", Value.from(1));
        va2.assign("e", Value.from(2));
        va2.assign("f", Value.from(3));

        va3 = new VariableAssignment(null);
        va3.declare("a", SimpleType.INT);
        va3.declare("b", SimpleType.INT);
        va3.declare("c", SimpleType.INT);
        va3.assign("a", Value.from(1));
        va3.assign("b", Value.from(3));
        va3.assign("c", Value.from(3));
    }

    @Test
    public void testjoinWithOutCheck1() {
        va1.joinWithoutCheck(va2);
        // Assert.assertEquals(6, va1.getValues().size());

    }

    @Test
    public void testjoinWithOutCheck2() {
        va1.joinWithoutCheck(va3);
        Assert.assertEquals(3, va1.getValues().size());

    }

    @Test
    public void testjoinWithCheck1() {
        VariableAssignment ret = va1.joinWithCheck(va2);
        // Assert.assertEquals(6, ret.getValues().size());

    }

    @Test
    public void testjoinWithCheck2() {
        VariableAssignment ret = va1.joinWithCheck(va3);
        Assert.assertEquals(0, ret.getValues().size());

    }
}
