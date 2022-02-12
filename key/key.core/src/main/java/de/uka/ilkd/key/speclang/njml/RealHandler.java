package de.uka.ilkd.key.speclang.njml;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.ldt.DoubleLDT;
import de.uka.ilkd.key.ldt.RealLDT;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.speclang.njml.OverloadedOperatorHandler.JMLOperator;

import java.util.EnumMap;
import java.util.Map;

import static de.uka.ilkd.key.speclang.njml.OverloadedOperatorHandler.JMLOperator.ADD;
import static de.uka.ilkd.key.speclang.njml.OverloadedOperatorHandler.JMLOperator.DIVISION;
import static de.uka.ilkd.key.speclang.njml.OverloadedOperatorHandler.JMLOperator.GT;
import static de.uka.ilkd.key.speclang.njml.OverloadedOperatorHandler.JMLOperator.GTE;
import static de.uka.ilkd.key.speclang.njml.OverloadedOperatorHandler.JMLOperator.LT;
import static de.uka.ilkd.key.speclang.njml.OverloadedOperatorHandler.JMLOperator.LTE;
import static de.uka.ilkd.key.speclang.njml.OverloadedOperatorHandler.JMLOperator.MODULO;
import static de.uka.ilkd.key.speclang.njml.OverloadedOperatorHandler.JMLOperator.MULT;
import static de.uka.ilkd.key.speclang.njml.OverloadedOperatorHandler.JMLOperator.SUBTRACT;
import static de.uka.ilkd.key.speclang.njml.OverloadedOperatorHandler.JMLOperator.UNARY_MINUS;

public class RealHandler extends LDTHandler {

    private final Map<JMLOperator, Operator> opMap =
            new EnumMap<>(JMLOperator.class);

    public RealHandler(Services services) {
        super(services);

        RealLDT realLDT = services.getTypeConverter().getRealLDT();

        opMap.put(ADD, realLDT.getAdd());
        opMap.put(SUBTRACT, realLDT.getSub());
        opMap.put(MULT, realLDT.getMul());
        opMap.put(DIVISION, realLDT.getDiv());
        opMap.put(UNARY_MINUS, realLDT.getNegation());
        opMap.put(GT, realLDT.getGreaterThan());
        opMap.put(LT, realLDT.getLessThan());
        opMap.put(GTE, realLDT.getGreaterOrEquals());
        opMap.put(LTE, realLDT.getLessOrEquals());
    }

    @Override
    protected Map<JMLOperator, Operator> getOperatorMap(Type promotedType) {
        if(promotedType == PrimitiveType.JAVA_REAL) {
            return opMap;
        } else {
            return null;
        }
    }

}
