package de.uka.ilkd.key.testgen.oracle;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.IfThenElse;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.Quantifier;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.logic.sort.SortImpl;
import de.uka.ilkd.key.smt.NumberTranslation;
import de.uka.ilkd.key.testgen.ReflectionClassCreator;
import de.uka.ilkd.key.testgen.TestCaseGenerator;
import de.uka.ilkd.key.testgen.oracle.OracleUnaryTerm.Op;

/**
 * Generator class for noninterference oracles. The class can generate the
 * oracle Method with the postcondition to check the noninterference property
 * @author Muessig
 *
 */
public class OracleGeneratorNoninterference extends OracleGenerator {

    /**
     * set of primitive data types
     */
    private Set<String> primitiveTypes;
    /**
     * for remembering objects which are already checked for isomorphic
     */
    private Set<String> newObjectsList;

    private boolean checkSameTypeGenerated;
    private boolean isomorphicCheckGenerated;
    private boolean helpIsomorphicCheckGenerated;
    
    /**
     *
     * @param services
     *            {@link Services}
     * @param rflCreator
     *            The {@link ReflectionClassCreator} for the rlf usage
     * @param useRFL
     *            true if rfl will be used for test case generation
     */
    public OracleGeneratorNoninterference(Services services,
            ReflectionClassCreator rflCreator, boolean useRFL) {
        super(services, rflCreator, useRFL);
        newObjectsList = new HashSet<String>();
        primitiveTypes = new HashSet<String>();
        addPrimitiveTypes();
    }

    private void addPrimitiveTypes() {
        primitiveTypes.add("boolean");
        primitiveTypes.add("char");
        primitiveTypes.add("int");
        primitiveTypes.add("long");
        primitiveTypes.add("float");
        primitiveTypes.add("double");
        primitiveTypes.add("short");
        primitiveTypes.add("byte");
        primitiveTypes.add("void");
    }

    @Override
    public OracleMethod generateOracleMethod(Term term) {
        // newObjectsList = new HashSet<String>();
        newObjectsList.clear();
        checkSameTypeGenerated = false;
        isomorphicCheckGenerated = false;
        helpIsomorphicCheckGenerated = false;
        constants = getConstants(term);
        methodArgs = getMethodArgs(term);
        OracleTerm body = generateOracle(term, false);
        if (body == null) {
            // empty Oracle
            System.out.println("Warning: the testOracle is empty");
            List<OracleVariable> emptyArgs = new LinkedList<OracleVariable>();
            return new OracleMethod("testOracle", emptyArgs, "return true");
        }
        return new OracleMethod("testOracle", methodArgs, "return " + body.toString() + ";");
    }

    @Override
    protected List<OracleVariable> getMethodArgs(Term t) {

        List<OracleVariable> result = new LinkedList<OracleVariable>();

        Sort allIntSort = createSetSort("Integer");
        Sort allBoolSort = createSetSort("Boolean");
        Sort allObjSort = createSetSort("java.lang.Object");

        OracleVariable allInts = new OracleVariable(TestCaseGenerator.ALL_INTS, allIntSort);
        OracleVariable allBools = new OracleVariable(TestCaseGenerator.ALL_BOOLS, allBoolSort);
        OracleVariable allObj = new OracleVariable(TestCaseGenerator.ALL_OBJECTS, allObjSort);
        boolean add = true;
        for (Term c : constants) {
            OracleVariable constant = new OracleVariable(c.toString().
                    replaceAll(AT_POST, ""), c.sort());

            // add constants just once
            for (OracleVariable o : result) {
                if (o.getName().toString().equals(constant.getName().toString())) {
                    add = false;

                }
            }
            if (add) {
                result.add(constant);
                // result.add(preConstant);
            }
        }

        result.add(allBools);
        result.add(allInts);
        result.add(allObj);
        return result;
    }

    // TODO test if the generation works with override and inheritance of helper
    // methods !
    // this would solve the code duplication problem
    // TODO method is to long
    /**
     * Generates the oracle method (with help-methods) for the given
     * {@link Term} term (postcondition).
     * @param term
     *            The postcondition you want to check with the Oracle
     * @param initialSelect
     * @return An {@link OracleMethodCall} for the generated oracle method.
     */
    @Override
    public OracleTerm generateOracle(Term term, boolean initialSelect) {
        Operator op = term.op();
        
        // binary terms
        if (ops.containsKey(op)) {

            if (equalLength(term)) {
                // compare length
                Term leftTerm = term.sub(0).sub(0);
                Term rightTerm = term.sub(1).sub(0);

                OracleMethod compareLengthMethod = oracleMethodCompareLength(leftTerm, rightTerm);
                List<OracleTerm> args;
                oracleMethods.add(compareLengthMethod);
                args = new LinkedList<OracleTerm>();
                args.addAll(quantifiedVariables);
                args.addAll(methodArgs);

                return new OracleMethodCall(compareLengthMethod, args);
            } else if(objectIsomorphicCheck(term)) { //compare objects -> check if objects isomorphic
                //TODO IDEA: recursive for each == check if we compare objects -> remember those
                //TODO at the end generate the isomorphic check for those objects (maybe with a second oracle Method which we have to call in each testcase 
                OracleMethod method = createObjectsIsormophicOracleMethod(term.sub(0), term.sub(1), initialSelect);
                oracleMethods.add(method);
                List<OracleTerm> args = new LinkedList<OracleTerm>();
                args.addAll(quantifiedVariables);
                args.addAll(methodArgs);
                return new OracleMethodCall(method, args);
            } else if (isAllFieldsEquals(term)) {
                // compare all fields
                // Equals with allFields (AllFields(a) == AllFields(b))
                Term leftTerm = term.sub(0).sub(0);
                Term rightTerm = term.sub(1).sub(0);

                String rightSort = leftTerm.sort().name().toString();
                String leftSort = rightTerm.sort().name().toString();
                OracleMethod method;
                List<OracleTerm> args;

                // AllFields for Array with same Type? (a[*] == b[*])
                if (leftSort.endsWith("[]") && leftSort.endsWith("[]")
                        && rightSort.equals(leftSort)) {

                    method = allFieldsArrayEqualsToMethod(leftTerm, rightTerm, initialSelect);

                    oracleMethods.add(method);
                    args = new LinkedList<OracleTerm>();
                    args.addAll(quantifiedVariables);
                    args.addAll(methodArgs);
                } else {
                    throw new RuntimeException("Could not translate oracle for: "
                            + term + " of type " + term.op());
                }

                return new OracleMethodCall(method, args);
            }

            // check subterm isomorphic -> remember objects and don't use them
            // for determine oracle
            // generate the isomorphic method first and remember the objects
            OracleTerm right;
            OracleTerm left;
            if (term.sub(1).op() instanceof Function
                    && term.sub(1).op().name().toString().equals("newObjectsIsomorphic")) {
                right = generateOracle(term.sub(1), initialSelect);
                left = generateOracle(term.sub(0), initialSelect);
            } else {
                left = generateOracle(term.sub(0), initialSelect);
                right = generateOracle(term.sub(1), initialSelect);
            }

            // empty right or empty left
            // left or right part of the formula may be null because of
            // isomorphic check
            if (right == null) {
                return left;
            }

            if (left == null) {
                return right;
            }

            String javaOp = ops.get(op);

            if (javaOp.equals(EQUALS)) {
                // equals check with objects already checked with
                // newObjectsIsomorphic -> don't check them with equal
                if (newObjectsList.contains(left.toString())
                        && newObjectsList.contains(right.toString())) {
                    return null;
                } else {
                    return eq(left, right);
                }
            } else if (javaOp.equals(AND)) {

                return and(left, right);
            } else if (javaOp.equals(OR)) {
                return or(left, right);
            }

            return new OracleBinTerm(javaOp, left, right);
        } else if (op == Junctor.NOT) {
            // negation
            OracleTerm sub = generateOracle(term.sub(0), initialSelect);

            // empty sub
            if (sub == null) {
                return null;
            }

            if (sub instanceof OracleUnaryTerm) {
                OracleUnaryTerm neg = (OracleUnaryTerm) sub;
                return neg.getSub();
            }
            return new OracleUnaryTerm(sub, Op.Neg);
        } else if (op == Junctor.TRUE) {
            // true
            return OracleConstant.TRUE;
        } else if (op == Junctor.FALSE) {
            // false
            return OracleConstant.FALSE;
        } else if (op == Junctor.IMP) {
            // imp - if imp is outer operation, then left term is in pre state
            // TODO pre state is not needed ? check this ! we just check the
            // postcondition !!
            OracleTerm left;
            OracleTerm right;
            // if (firstCall) {
            // left term from imp need pre state !!!
            left = generateOracle(term.sub(0), initialSelect);
            right = generateOracle(term.sub(1), initialSelect);
            // } else {
            // left = generateNoninterferenceOracle(term.sub(0),
            // initialSelect, false, needPrestate);
            // right = generateNoninterferenceOracle(term.sub(1),
            // initialSelect, false, needPrestate);
            // }
            if (left == null) {
                return right;
            } else if (right == null) {
                return neg(left);
            }
            OracleTerm notLeft = neg(left);
            return new OracleBinTerm(OR, notLeft, right);
        } else if (op instanceof QuantifiableVariable) { // quantifiable
                                                         // variable
            QuantifiableVariable qop = (QuantifiableVariable) op;
            // if (needPrestate) {
            // return new OracleVariable(PRE_STRING +
            // qop.name().toString().replaceAll(AT_POST, ""), qop.sort());
            // } else {
            return new OracleVariable(qop.name().toString().replaceAll(AT_POST, ""), qop.sort());
            // }
        } else if (op == services.getTypeConverter().getIntegerLDT().getNumberSymbol()) {
            // integers
            long num = NumberTranslation.translate(term.sub(0)).longValue();
            return new OracleConstant(Long.toString(num), term.sort());
        } else if (op == Quantifier.ALL || op == Quantifier.EX) { // forall
            Sort field = services.getTypeConverter().getHeapLDT().getFieldSort();
            Sort heap = services.getTypeConverter().getHeapLDT().targetSort();
            Sort varSort = term.boundVars().get(0).sort();
            if (varSort.equals(field) || varSort.equals(heap)) {
                return OracleConstant.TRUE;
            }

            OracleMethod method = createQuantifierMethod(term, initialSelect);
            oracleMethods.add(method);
            List<OracleTerm> args = new LinkedList<OracleTerm>();
            args.addAll(quantifiedVariables);
            args.addAll(methodArgs);
            return new OracleMethodCall(method, args);
        } else if (op == IfThenElse.IF_THEN_ELSE) { // if-then-else
            OracleMethod method = createIfThenElseMethod(term, initialSelect);
            oracleMethods.add(method);
            List<OracleTerm> args = new LinkedList<OracleTerm>();
            args.addAll(quantifiedVariables);
            args.addAll(methodArgs);
            return new OracleMethodCall(method, args);
        } else if (op instanceof Function) { // functions
            return translateFunction(term, initialSelect);
        } else if (op instanceof ProgramVariable) { // program variables
            ProgramVariable var = (ProgramVariable) op;
            LocationVariable loc = (LocationVariable) var;
            // if (needPrestate) {
            // // generate name with pre state !
            // return new OracleConstant(PRE_STRING
            // + loc.name().toString().replaceAll(AT_POST, ""), loc.sort());
            // } else {
            return new OracleConstant(loc.name().toString().replaceAll(AT_POST, ""), loc.sort());
            // }
        } else {
            // System.out.println("Could not translate: "+term);
            throw new RuntimeException("Could not translate oracle for: "
                    + term + " of type " + term.op());
        }

    }

    // TODO method is to long
    private OracleTerm translateFunction(Term term, boolean initialSelect) {
        Operator op = term.op();
        Function fun = (Function) op;
        String name = fun.name().toString();

        if (isTrueConstant(op)) {
            return OracleConstant.TRUE;
        } else if (isFalseConstant(op)) {
            return OracleConstant.FALSE;
        } else if (truePredicates.contains(name)) {
            return OracleConstant.TRUE;
        } else if (falsePredicates.contains(name)) {
            return OracleConstant.FALSE;
        } else if (term.arity() == 0) {
            return new OracleConstant(name, term.sort());
        } else if (name.endsWith("select")) {

            return translateSelect(term, initialSelect);
        } else if (name.equals("arr")) {
            OracleTerm index = generateOracle(term.sub(0), initialSelect);
            return new OracleConstant("[" + index + "]", term.sort());
        } else if (name.equals("length")) {
            OracleTerm o = generateOracle(term.sub(0), initialSelect);
            return new OracleConstant(o + ".length", term.sort());
        } else if (name.endsWith("::<inv>")) {

            if (fun instanceof IObserverFunction) {

                return oracleCallForInv(fun, initialSelect, term);

            }
        } else if (name.endsWith("::instance")) {

            if (fun instanceof SortDependingFunction) {
                SortDependingFunction sdf = (SortDependingFunction) fun;
                Sort s = sdf.getSortDependingOn();

                OracleTerm arg = generateOracle(term.sub(0), initialSelect);
                OracleType type = new OracleType(s);

                return new OracleBinTerm("instanceof", arg, type);

            }

        } else if (op instanceof ProgramMethod) {
            return translateQuery(term, initialSelect, op);

        } else if (name.equals("javaUnaryMinusInt")) {
            OracleTerm sub = generateOracle(term.sub(0), initialSelect);
            return new OracleUnaryTerm(sub, Op.Minus);
        } else if (name.equals("newObjectsIsomorphic")) {
            OracleMethod method = createNewIsomorphicOracleMethod(term,
                    initialSelect/* not needed */);
            if (method == null) {
                return null;
            }
            oracleMethods.add(method);
            List<OracleTerm> args = new LinkedList<OracleTerm>();
            args.addAll(quantifiedVariables);
            args.addAll(methodArgs);
            return new OracleMethodCall(method, args);
        }
        throw new RuntimeException("Unsupported function found: "
                + name + " of type " + fun.getClass().getName());
    }

    private OracleMethodCall oracleCallForInv(Function fun, Boolean initialSelect, Term term) {

        IObserverFunction obs = (IObserverFunction) fun;

        Sort s = obs.getContainerType().getSort();
        OracleMethod m;

        if (invariants.containsKey(s)) {
            m = invariants.get(s);
        } else {
            // needed for recursive invariants
            m = createDummyInvariant(s);
            invariants.put(s, m);

            m = createInvariantMethod(s, initialSelect);
            invariants.put(s, m);
            oracleMethods.add(m);
        }

        Term heap = term.sub(0);
        OracleTerm heapTerm = generateOracle(heap, initialSelect);

        Term object = term.sub(1);
        OracleTerm objTerm = generateOracle(object, initialSelect);

        if (isPreHeap(heapTerm)) { // delete if pre is already set with
                                   // "needPrestate"
            if (!objTerm.toString().startsWith(PRE_STRING)) {
                prestateTerms.add(objTerm.toString());
                objTerm = new OracleConstant(PRE_STRING + object.toString(), object.sort());
            }
        }

        List<OracleTerm> args = new LinkedList<OracleTerm>();
        args.add(objTerm);
        args.addAll(quantifiedVariables);
        args.addAll(methodArgs);

        return new OracleMethodCall(m, args);
    }
    
    private boolean checkJavaOpEquals(Term term) {
        Operator op = term.op();
        String javaOp = ops.get(op);
        if (javaOp.equals(EQUALS)) {
            return true;
        }
        return false;
    }
    
    private boolean objectIsomorphicCheck(Term term) {
        if (checkJavaOpEquals(term)) {
            Term left = term.sub(0);
            Term right = term.sub(1);
            Operator leftOp = left.op();
            Operator rightOp = right.op();
            if (leftOp instanceof ProgramVariable 
                    && rightOp instanceof ProgramVariable) {
                ProgramVariable leftVar = (ProgramVariable) leftOp;
                ProgramVariable rightVar = (ProgramVariable) rightOp;
                if (!primitiveTypes.contains(leftVar.sort().name().toString()) //eq with two objects ? 
                        && !primitiveTypes.contains(rightVar.sort().name().toString())
                        && leftVar.sort().name().toString().equals(rightVar.sort().name().toString())) {
                    System.out.println("compare two objects: check isomoprhic"); //TODO remove
                    return true;
                }
                
                System.out.println("Sort left: " + leftVar.sort().name().toString()); //TODO remove
                System.out.println("Sort right: " + rightVar.sort().name().toString()); //TODO remove
            } 
            
            else if (leftOp instanceof Function // eq with two select functions for objects ?
                    && rightOp instanceof Function) {
                Function leftFun = (Function) leftOp;
                Function rightFun = (Function) rightOp;
                String leftName = leftFun.name().toString();
                String rightName = rightFun.name().toString();
                
                if (leftName.endsWith("select") && rightName.endsWith("select")) { //compare fields ?
                    //TODO check if the selected fields are objects -> create isomorphic check for them !
                    if (!primitiveTypes.contains(left.sort().name().toString())  //field type not primitive ?
                            && !primitiveTypes.contains(right.sort().name().toString()) 
                            && left.sort().name().toString().equals(right.sort().name().toString())) {
                        System.out.println("compare two objects: check isomoprhic"); //TODO remove
                        return true;
                    }
                }
            }
        }
        return false;
    }

    private boolean isAllFieldsEquals(Term term) {
//        Operator op = term.op();
//        String javaOp = ops.get(op);
        if (checkJavaOpEquals(term)) {
            Term left = term.sub(0);
            Term right = term.sub(1);
            if (left.op() instanceof Function && right.op() instanceof Function) {
                Function leftFun = (Function) left.op();
                Function rightFun = (Function) right.op();
                if (leftFun.name().toString().equals("allFields")
                        && rightFun.name().toString().equals("allFields")) {
                    return true;
                }
            }
        }
        return false;
    }

    private boolean equalLength(Term term) {
        Operator op = term.op();
        String javaOp = ops.get(op);
        if (javaOp.equals(EQUALS)) {
            Term left = term.sub(0);
            Term right = term.sub(1);
            if (left.op() instanceof Function && right.op() instanceof Function) {
                Function leftFun = (Function) left.op();
                Function rightFun = (Function) right.op();
                if (leftFun.name().toString().equals("length")
                        && rightFun.name().toString().equals("length")) {
                    return true;
                }
            }
        }
        return false;
    }

    private String[] getObjNamesFromList(Term t, int size) {
        int i = 0;
        String[] names = new String[size];
        for (Term a : t.subs()) {
            if (a.op().name().toString().equals("seqSingleton")) {
                a = a.sub(0);
            }
            String name;
            // check if function (select)
            if (a.op() instanceof Function) {
                OracleTerm subFunct = translateFunction(a, false);

                name = subFunct.toString();
            } else {
                name = a.toString();
            }

            if (!primitiveTypes.contains(a.sort().name().toString())) {
                name = name.replaceAll(AT_POST, "");
                names[i] = name;
                newObjectsList.add(name);
            }
            i++;
        }

        //TODO [0] dont abord here !
        // empty ?
        if (names[0] == null) {
            return null;
        }
        return names;
    }
    
    //TODO pass list of objects to check. (at the moment: for each isomorphic check a new oracle method )
    private OracleMethod createObjectsIsormophicOracleMethod (Term leftTerm, Term rightTerm, boolean initialSelect) { 
        String result = "";
        String methodName = generateMethodName();
        String tab = TestCaseGenerator.TAB;
        String nameLeft;
        String nameRight;
        
        if (leftTerm.op() instanceof Function && rightTerm.op() instanceof Function) {
            OracleTerm leftSelect = translateFunction(leftTerm, initialSelect); //objects to check
            OracleTerm rightSelect = translateFunction(rightTerm, initialSelect); 
            nameLeft = leftSelect.toString();
            nameRight = rightSelect.toString();
        } else {
            nameLeft = leftTerm.toString();
            nameRight = rightTerm.toString();
        }
        nameLeft.replaceAll(AT_POST, "");
        nameRight.replaceAll(AT_POST, "");
        
        String[] objANames = {nameLeft};
        String[] objBNames = {nameRight};
        
        result = result + generateObjectsListsOracle(objANames, objBNames, objANames.length); //generate object list string

        List<OracleVariable> args = new LinkedList<OracleVariable>();
        String name = "Object[]";
        Sort array = new SortImpl(new Name(name));
        
     // add same type oracle method
        args = new LinkedList<OracleVariable>(); //generate sameTypes method and method call
        args.add(new OracleVariable("l1", array));
        args.add(new OracleVariable("l2", array));
        OracleMethod checkSameType = sameTypeMethod(args);
        if (!checkSameTypeGenerated) {
            oracleMethods.add(checkSameType);
            checkSameTypeGenerated = true;
        }
        OracleMethodCall callTypeCheck = new OracleMethodCall(checkSameType, args);
        
     // check object isomorphic
        OracleMethod isomorphicMethod = checkIsomorphicMethod(args); //generate isomorphic check oracle method and method call
        if (!isomorphicCheckGenerated) {
            oracleMethods.add(isomorphicMethod);  
            isomorphicCheckGenerated = true;
        }
        OracleMethodCall callIsomorphicMethod = new OracleMethodCall(isomorphicMethod, args);
        
        result = result + "\n" + tab + tab + "return " + callTypeCheck + " && " + callIsomorphicMethod +";";
        
        //generate the main Oracle Method
        args = new LinkedList<OracleVariable>();
        args.addAll(quantifiedVariables);
        args.addAll(methodArgs);

        return new OracleMethod(methodName, args, result);
    }
    
    private String generateObjectsListsOracle(String[] objANames, String[] objBNames, int numberOfElements) {
        String objectsA = "{";
        String objectsB = "{";
        String tab = TestCaseGenerator.TAB;
        for (int i = 0; i < numberOfElements - 1; i++) {
            objectsA = objectsA + objANames[i] + ",";
            objectsB = objectsB + objBNames[i] + ",";
        }
        objectsA = objectsA + objANames[numberOfElements - 1] + "}";
        objectsB = objectsB + objBNames[numberOfElements - 1] + "}";

        String objectArrays = "\n"
                + tab + tab + "Object[] l1 = " + objectsA + ";" + "\n"
                + tab + tab + "Object[] l2 = " + objectsB + ";";
        return objectArrays;
    }

    // compare the new objects. Same Type, Same fileds with same values
    private OracleMethod createNewIsomorphicOracleMethod(Term term, boolean initialSelect) {

        String result = "";
        String methodName = generateMethodName();
        String tab = TestCaseGenerator.TAB;
        Term objectListA = term.sub(0);
        Term objectListB = term.sub(2);

        int listSize = objectListA.subs().size();
        if (listSize != objectListB.subs().size()) {
            throw new RuntimeException("Could not translate oracle for: "
                    + term + " of type " + term.op());
        }
        
        //System.out.println(listSize);
        
        // all objects in the list as String
        String[] objANames = getObjNamesFromList(objectListA, listSize);
        String[] objBNames = getObjNamesFromList(objectListB, listSize);
        // no objects to check -> just primitive types
        if (objANames == null || objBNames == null) {
            System.out.println("Warning: no objects to check for isomorphic");
            return null;
        }

        String objectArrays = generateObjectsListsOracle(objANames, objBNames, listSize);
//        String objectsA = "{";
//        String objectsB = "{";
//        for (int i = 0; i < listSize - 1; i++) {
//            objectsA = objectsA + objANames[i] + ",";
//            objectsB = objectsB + objBNames[i] + ",";
//        }
//        objectsA = objectsA + objANames[listSize - 1] + "}";
//        objectsB = objectsB + objBNames[listSize - 1] + "}";
//
//        String objectArrays = "\n"
//                + tab + tab + "Object[] l1 = " + objectsA + ";" + "\n"
//                + tab + tab + "Object[] l2 = " + objectsB + ";";

        result = result + objectArrays;
        // until here create the two lists -> now call next submethod

        // submethod checks if objects are new
        OracleMethod checkIsomorphism = areObjectsNew();
        oracleMethods.add(checkIsomorphism);
        List<OracleVariable> args = new LinkedList<OracleVariable>();
        String name = "Object[]";
        Sort array = new SortImpl(new Name(name));
        args.add(new OracleVariable("l1", array));
        args.add(new OracleVariable("allObjects", createSetSort("Object")));
        // call for A
        OracleMethodCall callNewA = new OracleMethodCall(checkIsomorphism, args);

        args = new LinkedList<OracleVariable>();
        args.add(new OracleVariable("l2", array));
        args.add(new OracleVariable("allObjects", createSetSort("Object")));
        // call for B
        OracleMethodCall callNewB = new OracleMethodCall(checkIsomorphism, args);

        result = result + "\n" + tab + tab + "return " + callNewA + " && " + callNewB;

        // add same type oracle method
        args = new LinkedList<OracleVariable>();
        args.add(new OracleVariable("l1", array));
        args.add(new OracleVariable("l2", array));
        OracleMethod checkSameType = sameTypeMethod(args);
        if (!checkSameTypeGenerated) {
            oracleMethods.add(checkSameType);
            checkSameTypeGenerated = true;
        }

        OracleMethodCall callTypeCheck = new OracleMethodCall(checkSameType, args);

        result = result + " && " + callTypeCheck;

        // check object isomorphic
        OracleMethod isomorphicMethod = checkIsomorphicMethod(args);
        if (!isomorphicCheckGenerated) {
            oracleMethods.add(isomorphicMethod);
            isomorphicCheckGenerated = true;
        }
        OracleMethodCall callIsomorphicMethod = new OracleMethodCall(isomorphicMethod, args);

        result = result + " && " + callIsomorphicMethod + ";";

        args = new LinkedList<OracleVariable>();
        args.addAll(quantifiedVariables);
        args.addAll(methodArgs);

        return new OracleMethod(methodName, args, result);
    }

    private OracleMethod checkIsomorphicMethod(List<OracleVariable> args) {
        String methodName = "objectsAreIsomoprhic";
        String tab = TestCaseGenerator.TAB;

        List<OracleVariable> argsHelp = new LinkedList<OracleVariable>();
        String objectArray = "Object[]";
        String object = "Object";
        Sort array = new SortImpl(new Name(objectArray));
        Sort objectSort = new SortImpl(new Name(object));
        argsHelp.add(new OracleVariable("l1", array));
        argsHelp.add(new OracleVariable("l2", array));
        argsHelp.add(new OracleVariable("o1", objectSort));
        argsHelp.add(new OracleVariable("o2", objectSort));
        OracleMethod helpIsomorphicCheck = isomorphicHelpMethod(argsHelp);
        if(!helpIsomorphicCheckGenerated) {
            oracleMethods.add(helpIsomorphicCheck);
            helpIsomorphicCheckGenerated = true;
        }
        OracleMethodCall helperCall = new OracleMethodCall(helpIsomorphicCheck, argsHelp);

        String body = "\n"
                + tab + tab + "for (int i = 0; i < l1.length; i++) {" + "\n"
                + tab + tab + tab + "Object o1 = l1[i];" + "\n"
                + tab + tab + tab + "Object o2 = l2[i];" + "\n"
                + tab + tab + tab + "if (!" + helperCall + ") return false;" + "\n"
                + tab + tab + "}" + "\n"
                + tab + tab + "return true;";

        return new OracleMethod(methodName, args, body);

    }

    private OracleMethod isomorphicHelpMethod(List<OracleVariable> args) {
        String methodName = "objectsIsIsomorphic";
        String tab = TestCaseGenerator.TAB;

        String body = "\n"
                + tab + tab + "for (int i = 0; i < l1.length; i++) {" + "\n"
                + tab + tab + tab + "if ( (l1[i] == o1) != (l2[i] == o2)) return false;" + "\n"
                + tab + tab + "}" + "\n"
                + tab + tab + "return true;";

        return new OracleMethod(methodName, args, body);
    }

    private OracleMethod sameTypeMethod(List<OracleVariable> args) {
        String methodName = "sameTypes";
        String tab = TestCaseGenerator.TAB;
        String body = "\n"
                + tab + tab + "for (int i = 0; i < l1.length; i++) {" + "\n"
                + tab + tab + tab + "if (l1[i] == null && l2[i] == null) return true;" + "\n"
                + tab + tab + tab + "if (l1[i] == null || l2[i] == null) return false;" + "\n"
                + tab + tab + tab
                + "if (!l1[i].getClass().equals(l2[i].getClass())) return false;" + "\n"
                + tab + tab + "}" + "\n"
                + tab + tab + "return true;";

        return new OracleMethod(methodName, args, body);
    }

    private OracleMethod areObjectsNew() {

        String methodName = "newObjects";

        String tab = TestCaseGenerator.TAB;
        String body = "\n"
                + tab + tab + "for (Object o1 : l) {" + "\n"
                + tab + tab + tab + "for (Object o2 : allObjects) {" + "\n"
                + tab + tab + tab + tab + "if (o1 == o2) return false;" + "\n"
                + tab + tab + tab + "}" + "\n"
                + tab + tab + "}" + "\n"
                + tab + tab + "return true;";

        List<OracleVariable> args = new LinkedList<OracleVariable>();
        String name = "Object[]";
        Sort array = new SortImpl(new Name(name));
        args.add(new OracleVariable("l", array));
        args.add(new OracleVariable("allObjects", createSetSort("Object")));
        return new OracleMethod(methodName, args, body);
    }

    private OracleMethod oracleMethodCompareLength(Term leftTerm, Term rightTerm) {
        String methodName = generateMethodName();
        String left = leftTerm.toString().replaceAll("AtPost", "");
        String right = rightTerm.toString().replaceAll("AtPost", "");

        String tab = TestCaseGenerator.TAB;
        String body = "\n"
                + tab + tab + "if(" + left + " " + EQUALS + " null "
                + AND + " " + right + " " + EQUALS + " null " + " ) return true;" + "\n"
                + tab + tab + "if(" + left + " " + EQUALS + " null " + OR + " "
                + right + " " + EQUALS + " null " + " ) return false;" + "\n"
                + tab + tab + "return (" + left
                + ".length" + " " + EQUALS + " " + right + ".length" + " );";

        List<OracleVariable> args = new LinkedList<OracleVariable>();
        args.addAll(quantifiedVariables);
        args.addAll(methodArgs);

        return new OracleMethod(methodName, args, body);
    }

    private OracleMethod allFieldsArrayEqualsToMethod(Term leftTerm,
            Term rightTerm, boolean initialSelect) {
        String methodName = generateMethodName();

        String left = leftTerm.toString().replaceAll("AtPost", "");
        String right = rightTerm.toString().replaceAll("AtPost", "");

        String tab = TestCaseGenerator.TAB;
        String body = "\n"
                + tab + "if(" + left + ".length" + EQUALS + right + ".length" + " ) {" + "\n"
                + tab + tab + "for(" + "int" + " " + "i" + " : " + TestCaseGenerator.ALL_INTS + "){"
                + "\n"
                + tab + tab + tab + "if(" + "0 <= i" + " && " + "i < " + left + ".length"
                + " && " + "!(" + left + "[i]" + EQUALS + right + "[i]" + ")){" + "\n"
                + tab + tab + tab + tab + "return false;" + "\n" + tab + tab + tab + "}" + "\n"
                + tab + tab + "}" + "\n"
                + tab + "} else {" + "\n"
                + tab + tab + "return false;" + "\n"
                + tab + "}" + "\n"
                + tab + "return true;";

        List<OracleVariable> args = new LinkedList<OracleVariable>();
        args.addAll(quantifiedVariables);
        args.addAll(methodArgs);
        return new OracleMethod(methodName, args, body);

    }

}
