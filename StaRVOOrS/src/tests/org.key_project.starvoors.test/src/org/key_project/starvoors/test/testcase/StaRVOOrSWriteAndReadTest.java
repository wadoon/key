package org.key_project.starvoors.test.testcase;

import java.nio.charset.Charset;

import org.junit.Test;
import org.key_project.starvoors.model.StaRVOOrSExecutionPath;
import org.key_project.starvoors.model.StaRVOOrSProof;
import org.key_project.starvoors.model.StaRVOOrSResult;
import org.key_project.starvoors.model.io.StaRVOOrSReader;
import org.key_project.starvoors.model.io.StaRVOOrSWriter;

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
      StaRVOOrSProof p1 = new StaRVOOrSProof("HashTable[HashTable::HashTable(int)].JML normal_behavior operation contract.0", "TODO:");
      p1.addPath(new StaRVOOrSExecutionPath("true", true, false, false, false, false, null));
      StaRVOOrSProof p2 = new StaRVOOrSProof("HashTable[HashTable::add(java.lang.Object,int)].JML normal_behavior operation contract.0", "TODO:");
      p2.addPath(new StaRVOOrSExecutionPath("self.h[self.hash_function(key)] = null", true, false, true, false, true, TerminationKind.EXCEPTIONAL));
      p2.addPath(new StaRVOOrSExecutionPath("!self.h[self.hash_function(key)] = null", false, true, false, true, false, TerminationKind.NORMAL));
      StaRVOOrSProof p3 = new StaRVOOrSProof("HashTable[HashTable::add(java.lang.Object,int)].JML normal_behavior operation contract.1", "TODO:");
      p3.addPath(new StaRVOOrSExecutionPath("true", true, true, true, false, false, TerminationKind.LOOP_BODY));
      StaRVOOrSProof p4 = new StaRVOOrSProof("HashTable[HashTable::hash_function(int)].JML normal_behavior operation contract.0", "TODO:");
      p4.addPath(new StaRVOOrSExecutionPath("val >  -1", true, true, false, false, true, null));
      p4.addPath(new StaRVOOrSExecutionPath("val < 0", true, false, false, false, true, null));
      StaRVOOrSResult result = new StaRVOOrSResult();
      result.addProof(p1);
      result.addProof(p2);
      result.addProof(p3);
      result.addProof(p4);
      return result;
   }
}
