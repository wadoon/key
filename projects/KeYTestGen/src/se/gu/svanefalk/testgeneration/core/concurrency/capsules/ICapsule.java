package se.gu.svanefalk.testgeneration.core.concurrency.capsules;

import se.gu.svanefalk.testgeneration.core.concurrency.monitor.ICapsuleMonitor;

public interface ICapsule extends Runnable {

    void doWork();

    void addMonitor(ICapsuleMonitor capsuleMonitor);
}
