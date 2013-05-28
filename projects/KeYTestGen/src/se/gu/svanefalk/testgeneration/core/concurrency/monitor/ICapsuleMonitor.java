package se.gu.svanefalk.testgeneration.core.concurrency.monitor;

import se.gu.svanefalk.testgeneration.core.concurrency.capsules.ICapsule;

public interface ICapsuleMonitor {

    void doNotify(ICapsule source, IMonitorEvent event);
}
