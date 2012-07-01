/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.util;

import java.text.DecimalFormat;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public final class DagOperationManager {

    /**
     * global counter to keep track of running DAG traversals.
     */
    private static long operationCount = 0;

    /**
     * The list of operations which have already finished.
     */
    private static final List<Long> finishedOperations = new ArrayList<Long>();

    /**
     * Stores the number of nodes which have been visitied by each operation.
     */
    private static final Map<Long, Long> nodeCounterPerOperation = new HashMap<Long, Long>();

    /**
     * Stores for each operation after how many nodes a message should be
     * displayed.
     */
    private static final Map<Long, Long> progressIncrement = new HashMap<Long, Long>();

    /**
     * Optionally stores a textual name for an operation.
     */
    private static final Map<Long, String> operationNames = new HashMap<Long, String>();

    /**
     * A formatter for printing numbers.
     */
    public static final DecimalFormat myFormatter = new DecimalFormat(
            "###,###,###");

    /**
     * @return the <code>operationCount</code>
     */
    public static long getOperationCount() {
        return DagOperationManager.operationCount;
    }

    /**
     * start a new DAG operation. increments global operation counter and
     * provides a unique operation id.
     * 
     * @return unique operation id.
     */
    public static long startDAGOperation() {
        DagOperationManager.operationCount++;
        assert (DagOperationManager.operationCount > 0);
        // System.out.println("Starting DAG operation " + Z3Proof.operationCount
        // + " in thread " + Thread.currentThread());
        return DagOperationManager.operationCount;
    }

    /**
     * Starts a new DAG operation and stores the given name for it.
     * 
     * @param name
     *            the name of the operation.
     * @return a unique operation id.
     */
    public static long startDAGOperation(String name) {
        long operationId = DagOperationManager.startDAGOperation();
        DagOperationManager.operationNames.put(operationId, name);
        return operationId;
    }

    /**
     * ends a DAG operation. decrements the global operation counter and removes
     * all <code>visitedByOperation</code> list entries for this operation in
     * all nodes.
     * 
     * @param operationId
     *            unique id of the operation to end.
     */
    public static void endDAGOperation(long operationId) {
        assert (DagOperationManager.operationCount >= operationId);
        DagOperationManager.finishedOperations.add(operationId);
        String operationName = DagOperationManager.operationNames
                .get(operationId);
        if (operationName != null) {
            Long counterObj = DagOperationManager.nodeCounterPerOperation
                    .get(operationId);

            String counterString = counterObj == null ? "(<increment)"
                    : DagOperationManager.myFormatter.format(counterObj
                            .longValue());
            System.out.println("PROGRESS-INFO: DAG operation " + operationName
                    + " finished with node counter value " + counterString
                    + ".");
        }

        // System.out.println("Stopped DAG operation " + Z3Proof.operationCount
        // + " in thread " + Thread.currentThread());

        // Reusing operation-IDs seems to cause problems under some
        // circumstances.
        // In particular, when the structure of the DAG is modified by the
        // operation. Thus, do not reuse operation-IDs.

        // Z3Proof.operationCount--;
    }

    /**
     * Increments the node counter for the given operation
     * 
     * @param operationId
     */
    public static void incrementNodeCounter(long operationId) {
        long currentValue = DagOperationManager.nodeCounterPerOperation
                .get(operationId);
        currentValue++;

        Long increment = DagOperationManager.progressIncrement.get(operationId);
        if (increment != null) {
            if (currentValue % increment.longValue() == 0) {
                String operationString = DagOperationManager
                        .getOperationName(operationId);
                if (operationString.equals(""))
                    operationString = DagOperationManager.myFormatter
                            .format(operationId);
                String counterString = DagOperationManager.myFormatter
                        .format(currentValue);
                System.out.println("PROGRESS-INFO: DAG operation "
                        + operationString + " is at node counter value "
                        + counterString + ".");
            }
        }

        DagOperationManager.nodeCounterPerOperation.put(operationId,
                currentValue);
    }

    public static void setMessageInterval(long operationId, long increment) {
        DagOperationManager.progressIncrement.put(operationId, increment);
    }

    /**
     * 
     * @return a read-only version of the list of finished operations.
     */
    public static List<Long> getFinishedOperations() {
        return Collections
                .unmodifiableList(DagOperationManager.finishedOperations);
    }

    /**
     * Returns the name of an operation
     * 
     * @param operationId
     *            the id of the operation for which the name is seeked.
     * @return the name of the operation or an empty string, if none is found.
     */
    public static String getOperationName(long operationId) {
        String result = DagOperationManager.operationNames.get(operationId);
        return ((result == null) ? "" : result);
    }
}
