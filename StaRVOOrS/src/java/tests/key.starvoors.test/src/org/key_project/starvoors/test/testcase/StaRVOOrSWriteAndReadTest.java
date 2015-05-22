package org.key_project.starvoors.test.testcase;

import java.nio.charset.Charset;
import java.util.List;

import org.junit.Test;
import org.key_project.starvoors.model.StaRVOOrSExecutionPath;
import org.key_project.starvoors.model.StaRVOOrSLoopInvariantApplication;
import org.key_project.starvoors.model.StaRVOOrSMethodContractApplication;
import org.key_project.starvoors.model.StaRVOOrSProof;
import org.key_project.starvoors.model.StaRVOOrSResult;
import org.key_project.starvoors.model.io.StaRVOOrSReader;
import org.key_project.starvoors.model.io.StaRVOOrSWriter;
import org.key_project.util.java.CollectionUtil;

import de.uka.ilkd.key.symbolic_execution.model.IExecutionTermination.TerminationKind;

public class StaRVOOrSWriteAndReadTest extends AbstractStaRVOOrSTest {
   @Test
   public void testWritingAndReading() throws Exception {
      StaRVOOrSResult expected = createExpectedHashtableResult();
      String xml = StaRVOOrSWriter.toXML(expected, Charset.defaultCharset().displayName());
      StaRVOOrSResult actual = StaRVOOrSReader.load(xml);
      assertResult(expected, actual);
   }
   
   protected static StaRVOOrSResult createExpectedHashtableResult() {
      StaRVOOrSMethodContractApplication ma1 = new StaRVOOrSMethodContractApplication("mafile1", 11, 22, 33, 44, "type1", "method1", "contract1");
      StaRVOOrSMethodContractApplication ma2 = new StaRVOOrSMethodContractApplication("mafile2", 111, 222, 333, 444, "type2", "method2", "contract2");
      List<StaRVOOrSMethodContractApplication> maa1 = CollectionUtil.toList(ma1);
      List<StaRVOOrSMethodContractApplication> maa2 = CollectionUtil.toList(ma2);
      List<StaRVOOrSMethodContractApplication> maa1a2 = CollectionUtil.toList(ma1, ma2);
      StaRVOOrSLoopInvariantApplication la1 = new StaRVOOrSLoopInvariantApplication("lafile1", -4, -3, -2, -1);
      StaRVOOrSLoopInvariantApplication la2 = new StaRVOOrSLoopInvariantApplication("lafile2", -44, -33, -22, -11);
      List<StaRVOOrSLoopInvariantApplication> laa1 = CollectionUtil.toList(la1);
      List<StaRVOOrSLoopInvariantApplication> laa2 = CollectionUtil.toList(la2);
      List<StaRVOOrSLoopInvariantApplication> laa1a2 = CollectionUtil.toList(la1, la2);
      StaRVOOrSProof p1 = new StaRVOOrSProof("HashTable[HashTable::HashTable(int)].JML normal_behavior operation contract.0", "TODO:", "type", "target");
      p1.addPath(new StaRVOOrSExecutionPath("true", true, null, null, null, null, null, null));
      StaRVOOrSProof p2 = new StaRVOOrSProof("HashTable[HashTable::add(java.lang.Object,int)].JML normal_behavior operation contract.0", "TODO:", "type", "target");
      p2.addPath(new StaRVOOrSExecutionPath("self.h[self.hash_function(key)] = null", true, maa1, null, laa1, null, TerminationKind.EXCEPTIONAL, "newPrecondition"));
      p2.addPath(new StaRVOOrSExecutionPath("!self.h[self.hash_function(key)] = null", false, null, maa1, null, laa1, TerminationKind.NORMAL, "aDifferentPrecondition"));
      StaRVOOrSProof p3 = new StaRVOOrSProof("HashTable[HashTable::add(java.lang.Object,int)].JML normal_behavior operation contract.1", "TODO:", "type", "target");
      p3.addPath(new StaRVOOrSExecutionPath("true", true, null, null, laa1, laa2, TerminationKind.LOOP_BODY, null));
      StaRVOOrSProof p4 = new StaRVOOrSProof("HashTable[HashTable::hash_function(int)].JML normal_behavior operation contract.0", "TODO:", "type", "target");
      p4.addPath(new StaRVOOrSExecutionPath("val >  -1", true, null, maa1a2, laa1a2, null, null, null));
      p4.addPath(new StaRVOOrSExecutionPath("val < 0", true, maa1, maa2, laa1a2, null, null, null));
      StaRVOOrSResult result = new StaRVOOrSResult();
      result.addProof(p1);
      result.addProof(p2);
      result.addProof(p3);
      result.addProof(p4);
      return result;
   }
}
