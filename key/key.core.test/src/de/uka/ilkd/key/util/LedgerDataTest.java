package de.uka.ilkd.key.util;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.logic.sort.SortImpl;
import de.uka.ilkd.key.rule.TacletForTests;
import org.junit.Before;
import org.junit.Test;

public class LedgerDataTest {
    private Services s;
    private NamespaceSet nss;
    private TermBuilder tb;
    private static Sort intType;
    private static Sort boolType;
    private static Sort heapType;
    private static Sort objectType;
    private static Sort fieldType;
    private static Sort intArrayType;

    LedgerDataTacletGenerator gen;

//    File file = new File("/home/i57/cnodes/jschiffl/tmp/smttest/smttestfile");
//    File castTestFile = new File("/home/i57/cnodes/jschiffl/tmp/smttest/CastTest.java");
//    FileWriter fw = null;
//    BufferedWriter writer = null;

    @Before
    public void setup() {
        this.s = TacletForTests.services();
        nss = s.getNamespaces();
        intType = nss.sorts().lookup("int");
        boolType = nss.sorts().lookup("boolean");
        heapType = nss.sorts().lookup("Heap");
        objectType = nss.sorts().lookup("java.lang.Object");
        fieldType = nss.sorts().lookup("Field");
        this.tb = s.getTermBuilder();
        Sort s = new SortImpl(new Name("TestSort"));
    }

    @Test
    public void test() {
    }



}

class TestClass1 extends org.hyperledger.fabric.shim.LedgerData {

    public static int x;

    @Override
    public byte[] serialize(org.hyperledger.fabric.shim.LedgerData ld) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public org.hyperledger.fabric.shim.LedgerData deserialize(byte[] b) {
        // TODO Auto-generated method stub
        return null;
    }

}

class TestClass2 extends org.hyperledger.fabric.shim.LedgerData {

    private boolean b;
    int y;
    TestClass1 tc1;

    @Override
    public byte[] serialize(org.hyperledger.fabric.shim.LedgerData ld) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public org.hyperledger.fabric.shim.LedgerData deserialize(byte[] b) {
        // TODO Auto-generated method stub
        return null;
    }

}
