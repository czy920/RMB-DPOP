package edu.cqu.algorithms;

import edu.cqu.core.Message;
import edu.cqu.core.SyncMailer;
import edu.cqu.ordering.DFSSyncAgent;
import edu.cqu.result.ResultCycle;
import java.util.*;

public class RMBDPOP extends DFSSyncAgent {
    private static final int K = 3;

    private static final int MSG_SEP_INFO = 0;
    private static final int MSG_LABEL = 1;
    private static final int MSG_NORMAL_UTIL = 2;
    private static final int MSG_CONTEXT = 3;
    private static final int MSG_START = 4;
    private static final int MSG_UTIL = 5;
    private static final int MSG_SEP_DEGREE = 6;
    private static final int MSG_ALLOCATION = 7;
    private static final int MSG_DPOP_START = 8;
    private static final int MSG_VALUE = 9;
    private static final int MSG_CC_VALUE = 10;
    private static final int MSG_CC_INFERENCE = 11;

    private enum NodeType {
        NORMAL, CLUSTER_ROOT, UNDETERMINED
    }

    private boolean isClusterLeaf;
    private int LABEL_COUNT;
    private NodeType nodeType;
    private Map<Integer, NDimData> localUtilities;
    private Map<Integer, Integer> sepDomainLength;
    private Map<Integer, Integer> sepLevel;
    private Map<Integer, Set<Integer>> childrenCCList;
    private int numNormalUtilityReceived;
    private List<NDimData> normalUtilities;
    private SearchSpace searchSpace; // only used in cluster root
    private Map<Integer, Integer> context;
    private NDimData localUtility; // used only in cluster root: just a trick to reduce the computation effort
    private Map<Integer, Integer> ccDomainLength;
    private Map<Integer, NDimData> childrenUtilities; // only used in nodes in a cluster
    private NDimData sepCache;
    private Map<Integer,Map<Integer,Integer>> lastContext2child;
    private Map<Integer, DRInfo> DR;//dimension reduction
    private List<Integer> CCList;
    private int ddr;//descendants dimension reduction
    private int drReceivedCount;
    private int DR_COUNT;
    private int ccNow;
    private int curVal;
    private Map<Integer,Integer> sepValue;
    private Map<Integer, Integer> fixedValues;

    public RMBDPOP(int id, int[] domain, int[] neighbours, Map<Integer, int[][]> constraintCosts, Map<Integer, int[]> neighbourDomains, SyncMailer mailer) {
        super(id, domain, neighbours, constraintCosts, neighbourDomains, mailer);
        this.nodeType = NodeType.UNDETERMINED;
        this.localUtilities = new HashMap<>();
        this.sepDomainLength = new HashMap<>();
        this.sepLevel = new HashMap<>();
        this.childrenCCList = new HashMap<>();
        this.ccDomainLength = new HashMap<>();
        this.childrenUtilities = new HashMap<>();
        this.normalUtilities = new ArrayList<>();
        this.CCList = new ArrayList<>();
        this.DR = new HashMap<>();
        this.ccNow = -1;
        this.LABEL_COUNT = 0;
        this.sepValue = new HashMap<>();
        this.fixedValues = new HashMap<>();
    }

    @Override
    protected void pseudoTreeCreated() {
        DR_COUNT = children.size();
        for (int pp : this.pseudoParents) {
            this.localUtilities.put(pp, NDimData.fromConstraint(this.constraintCosts.get(pp), this.id, pp));
        }
        if (isRootAgent()) {
            for (int c : this.children) {
                Map<Integer, Integer> sepDomainLength = new HashMap<>();
                Map<Integer, Integer> sepLevel = new HashMap<>();
                sepDomainLength.put(this.id, this.domain.length);
                sepLevel.put(this.id, this.level);
                sendMessage(new Message(this.id, c, MSG_SEP_INFO, new SepInfo(sepDomainLength, sepLevel)));
            }
        } else {
            this.localUtilities.put(this.parent, NDimData.fromConstraint(this.constraintCosts.get(this.parent), this.id, this.parent));
        }
    }

    @Override
    public void disposeMessage(Message message) {
        super.disposeMessage(message);
        switch (message.getType()) {
            case MSG_SEP_INFO:
                SepInfo sepInfo = (SepInfo) message.getValue();
                for (int id : this.sep) {
                    this.sepDomainLength.put(id, sepInfo.sepDomainLength.get(id));
                    this.sepLevel.put(id, sepInfo.sepLevel.get(id));
                }
                for (int c : this.children) {
                    Map<Integer, Integer> sepDomainLength = new HashMap<>(this.sepDomainLength);
                    Map<Integer, Integer> sepLevel = new HashMap<>(this.sepLevel);
                    sepDomainLength.put(this.id, this.domain.length);
                    sepLevel.put(this.id, this.level);
                    sendMessage(new Message(this.id, c, MSG_SEP_INFO, new SepInfo(sepDomainLength, sepLevel)));
                }
                if (isLeafAgent()) {
                    if(sep.size() <= K)
                        this.nodeType = NodeType.NORMAL;
                    sendMessage(new Message(this.id, this.parent, MSG_LABEL,sep.size() - K ));
                }
                break;
            case MSG_LABEL:
                int redundancy  = (int) message.getValue();
                LABEL_COUNT++;
                if(redundancy <= 0)
                    DR_COUNT--;
                if (LABEL_COUNT == children.size()) {
                    if (!isRootAgent()) {
                        if (this.sep.size() <= K) {
                            if (DR_COUNT != 0) {
                                this.nodeType = NodeType.CLUSTER_ROOT;
                                this.localUtility = NDimData.merge(new ArrayList<>(this.localUtilities.values())); // localUtility never exceeds K, so it is safe
                                this.sepCache = new NDimData(this.sepDomainLength, Integer.MAX_VALUE);
                            }else {
                                this.nodeType = NodeType.NORMAL;
                            }
                        }
                        sendMessage(new Message(this.id, this.parent, MSG_LABEL, sep.size()-K));
                    } else {
                        // root
                        this.nodeType = NodeType.NORMAL;
                        for (int c : this.children) {
                            sendMessage(new Message(this.id, c, MSG_START, null));
                        }
                    }
                }
                break;
            case MSG_START:
                isClusterLeaf = (sep.size() > K ) && (DR_COUNT == 0);
                if(isClusterLeaf){
                    propagateSepDegree(ccNow);
                }
                if (isLeafAgent()) {
                    if (this.nodeType == NodeType.NORMAL){
                        NDimData res = NDimData.eliminate(new ArrayList<>(this.localUtilities.values()), this.id);
                        sendMessage(new Message(this.id, this.parent, MSG_NORMAL_UTIL, res));
                    }
                } else {
                    for (int c : this.children) {
                        sendMessage(new Message(this.id, c, MSG_START, null));
                    }
                }
                break;
            case MSG_SEP_DEGREE:
                drReceivedCount++;
                SepDegreeInfo receivedD = (SepDegreeInfo) message.getValue();
                if(receivedD.cc != -1){
                    if(ccNow == -1){
                        ccNow = receivedD.cc;
                        if(!CCList.contains(ccNow))
                            CCList.add(ccNow);
                    }
                    if(!childrenCCList.containsKey(message.getIdSender())) {
                        Set<Integer> temp = new HashSet<>();
                        temp.add(receivedD.cc);
                        childrenCCList.put(message.getIdSender(),temp);
                    } else
                        childrenCCList.get(message.getIdSender()).add( receivedD.cc);
                }

                for(int i : receivedD.sendDR.keySet()){
                    DRInfo temp = receivedD.sendDR.get(i);
                    if(this.DR.containsKey(i)){
                        int d = this.DR.get(i).degree + temp.degree;
                        this.DR.get(i).degree = d;
                        this.DR.get(i).lowestChildLevel = Integer.max(this.DR.get(i).lowestChildLevel, temp.lowestChildLevel);
                    }else{
                        this.DR.put(i,temp);
                    }
                }
                this.ddr = Integer.max(ddr, receivedD.sendddr);
                if(drReceivedCount == DR_COUNT){
                    if(nodeType != NodeType.CLUSTER_ROOT){
                        propagateSepDegree(ccNow);
                        ccNow = -1;
                    }else{
                        if(DR.size() == 0) {
                            Collections.sort(CCList);
                            propagateContext();
                            for (int c : this.children) {
                                sendMessage(new Message(this.id, c, MSG_DPOP_START, null));
                            }
                        } else {
                            int chooseOne = -1;
                            int maxD = Integer.MIN_VALUE;
                            Map<Integer,Integer> tie = new HashMap<>();
                            for(int i : this.DR.keySet()){
                                if(maxD < this.DR.get(i).degree){
                                    maxD = this.DR.get(i).degree;
                                    chooseOne = i;
                                }
                            }
                            for(int i : this.DR.keySet()){
                                if(maxD == this.DR.get(i).degree){
                                    tie.put(i,DR.get(i).level);
                                }
                            }

                            if(tie.size() > 1){
                                chooseOne = breakTie(tie);
                            }
                            CCList.add(chooseOne);
                            ccDomainLength.put(chooseOne,DR.get(chooseOne).domainLength);
                            DomainLength d = new DomainLength(chooseOne,DR.get(chooseOne).domainLength);
                            for(int c : children){
                                sendMessage(new Message(this.id, c, MSG_ALLOCATION, d));
                            }
                        }
                        reSet();
                    }
                }
                break;
            case MSG_DPOP_START:
                if(!isClusterLeaf){
                    for (int c : this.children) {
                        sendMessage(new Message(this.id, c, MSG_DPOP_START, null));
                    }
                }
                break;
            case MSG_ALLOCATION:
                if(nodeType == NodeType.CLUSTER_ROOT || nodeType == NodeType.NORMAL)
                    break;
                DomainLength recv = (DomainLength) message.getValue();
                if(sep.contains(recv.cc)|| this.id == recv.cc) {
                    CCList.add(recv.cc);
                    ccDomainLength.put(recv.cc,recv.domainLength);
                }
                reSet();
                if(!isClusterLeaf){
                    for(int c : children){
                        sendMessage(new Message(this.id, c, MSG_ALLOCATION, recv));
                    }
                }else {
                    propagateSepDegree(recv.cc);
                }
                break;
            case MSG_NORMAL_UTIL:
                NDimData receivedNormalUtility = (NDimData) message.getValue();
                normalUtilities.add(receivedNormalUtility);
                this.numNormalUtilityReceived++;
                if (normalUtilityReady()) {
                    if (this.nodeType == NodeType.NORMAL) {
                        if (!isRootAgent()) {
                            List<NDimData> allData = new ArrayList<>(this.localUtilities.values());
                            allData.addAll(this.normalUtilities);
                            NDimData res = NDimData.eliminate(allData, this.id);
                            sendMessage(new Message(this.id, this.parent, MSG_NORMAL_UTIL, res));
                        }
                        else {
                            NDimData util = NDimData.merge(this.normalUtilities);
                            int result = util.argMin(new HashMap<>());
                            this.valueIndex = result;
                            Map<Integer, Integer> res = new HashMap<>();
                            res.put(this.id, result);
                            for(int c: children){
                                sendMessage(new Message(id,c, MSG_VALUE,res));
                            }
                            stopProcess();
                        }
                    }
                    else if (boundedUtilityReady()&& context != null){
                        if(isCCNode())
                            updateNcheckVal();
                        else if (this.nodeType == NodeType.CLUSTER_ROOT){
                            List<NDimData> allData = new ArrayList<>(this.childrenUtilities.values());
                            allData.add(this.localUtility);
                            allData.addAll(this.normalUtilities);
                            this.sepCache.update(allData, this.context, this.id, this.domain.length);
                            this.searchSpace.next();
                            if (this.searchSpace.hasNext()){
                                propagateContext();
                            }
                            else {
                                NDimData res = this.sepCache.copy();
                                sendMessage(new Message(this.id, this.parent, MSG_NORMAL_UTIL, res));
                            }
                        }
                        else {
                            NDimData res = boundedInference();
                            sendMessage(new Message(this.id, this.parent, MSG_UTIL, res));
                        }
                    }
                }
                break;
            case MSG_CONTEXT:
                this.context = (Map<Integer, Integer>) message.getValue();
                if (isCCNode()){
                    Map<Integer,Integer> domainLength = new HashMap<>(sepDomainLength);
                    for(int i: sepDomainLength.keySet()){
                        if(context.containsKey(i)){
                            domainLength.remove(i);
                        }
                    }
                    sepCache = new NDimData(domainLength,Integer.MAX_VALUE);
                }
                if (this.childrenCCList.size() != 0)
                    propagateContext();
                else if (normalUtilityReady()){
                    // propagate bounded utility
                    NDimData res = boundedInference();
                    sendMessage(new Message(this.id, this.parent, MSG_UTIL, res));
                }
                break;
            case MSG_UTIL:
                NDimData receivedBoundedUtility = (NDimData)  message.getValue();
                this.childrenUtilities.put(message.getIdSender(), receivedBoundedUtility);
                if (normalUtilityReady() && boundedUtilityReady()){
                    if (this.nodeType == NodeType.CLUSTER_ROOT){
                        List<NDimData> allData = new ArrayList<>(this.childrenUtilities.values());
                        allData.add(this.localUtility);
                        allData.addAll(this.normalUtilities);
                        this.sepCache.update(allData, this.context, this.id, this.domain.length);
                        this.searchSpace.next();
                        if (this.searchSpace.hasNext()){
                            propagateContext();
                        }
                        else {
                            NDimData res = this.sepCache.copy();
                            sendMessage(new Message(this.id, this.parent, MSG_NORMAL_UTIL, res));
                        }
                    }
                    else {
                        if(isCCNode())
                            updateNcheckVal();
                        else{
                            NDimData res = boundedInference();
                            sendMessage(new Message(this.id, this.parent, MSG_UTIL, res));
                        }
                    }
                }
                break;
            case MSG_VALUE:
                Map<Integer, Integer> r = (Map<Integer, Integer>) message.getValue();
                sepValue.putAll(r);
                if (this.nodeType == NodeType.NORMAL) {
                    NDimData util = NDimData.merge(finalInference(sepValue));
                    int result = util.argMin(new HashMap<>());
                    this.valueIndex = result;
                    Map<Integer, Integer> res = sepValue;
                    res.put(this.id, result);
                    for (int c : children) {
                        sendMessage(new Message(id, c, MSG_VALUE, res));
                    }
                    stopProcess();
                } else if (this.nodeType == NodeType.CLUSTER_ROOT) {
                    childrenUtilities.clear();
                    Map<Integer, Integer> ccValue = new HashMap<>(sepValue);
                    ccValue.putAll(sepCache.assignStorage[sepCache.getIndex(sepValue)]);
                    for (int c : childrenCCList.keySet()) {
                        sendMessage(new Message(id, c, MSG_CC_VALUE, ccValue));
                    }
                } else {
                    int result = -1;
                    if (fixedValues.containsKey(this.id)) {
                        result = fixedValues.get(this.id);
                    } else {
                        NDimData res = NDimData.merge(finalInference(sepValue));
                        result = res.argMin(sepValue);
                    }
                    this.valueIndex = result;
                    Map<Integer, Integer> res = sepValue;
                    res.put(this.id, result);
                    for (int c : children) {
                        sendMessage(new Message(id, c, MSG_VALUE, res));
                    }
                    stopProcess();
                }
                break;
            case MSG_CC_VALUE:
                childrenUtilities.clear();
                Map<Integer,Integer> ccValue = (Map<Integer, Integer>) message.getValue();
                fixedValues = new HashMap<>(ccValue);
                for(int c: ccValue.keySet()){
                    if(sep.contains(c)){
                        sepValue.put(c,ccValue.get(c));
                    }
                }
                fixedValues.putAll(sepValue);
                if (this.childrenCCList.size() == 0){
                    List<NDimData> utilities = finalInference(fixedValues);
                    sendMessage(new Message(this.id, this.parent, MSG_CC_INFERENCE, NDimData.eliminate(utilities,this.id)));
                }
                else {
                    for(int c: childrenCCList.keySet()){
                        sendMessage(new Message(id,c, MSG_CC_VALUE,ccValue));
                    }
                }
                break;
            case MSG_CC_INFERENCE:
                int senderId = message.getIdSender();
                NDimData childUtil = (NDimData) message.getValue();
                childrenUtilities.put(senderId, childUtil);
                if(boundedUtilityReady()){
                    if(nodeType != NodeType.CLUSTER_ROOT) {
                        List<NDimData> utilities = finalInference(fixedValues);
                        sendMessage(new Message(this.id, this.parent, MSG_CC_INFERENCE, NDimData.eliminate(utilities, this.id)));
                    }else{
                        int result = (int) sepCache.assignStorage[sepCache.getIndex(sepValue)].get(this.id);
                        this.valueIndex = result;
                        Map<Integer, Integer> res = sepValue;
                        res.put(this.id, result);
                        for(int c: children){
                            sendMessage(new Message(id,c, MSG_VALUE,res));
                        }
                        stopProcess();
                    }
                }
                break;
        }
    }

    private List<NDimData> finalInference(Map<Integer,Integer> assignment){
        List<NDimData> utilities = new ArrayList<>();
        for(NDimData n : localUtilities.values()){
            NDimData data = n;
            for (int var: n.orderedId){
                if (assignment.containsKey(var)) {
                    data = data.restrict(assignment);
                    break;
                }
            }
            utilities.add(data);
        }
        for(NDimData data : normalUtilities) {
            for (int var : data.orderedId) {
                if (assignment.containsKey(var)) {
                    data = data.restrict(assignment);
                    break;
                }
            }
            utilities.add(data);
        }

        for(NDimData n : childrenUtilities.values()){
            NDimData data = n;
            for (int var: n.orderedId){
                if (assignment.containsKey(var)) {
                    data = data.restrict(assignment);
                    break;
                }
            }
            utilities.add(data);
        }
        return utilities;
    }

    private boolean isCCNode(){
        return this.nodeType != NodeType.CLUSTER_ROOT && this.CCList.contains(this.id);
    }

    private int breakTie(Map<Integer, Integer> tie) {
        int ret = 0;
        // ties broken by level
        List<Map.Entry<Integer,Integer>> sortedTie = new ArrayList<>(tie.entrySet());
        for(int i =0; i<sortedTie.size(); i++){
            int difference = DR.get(sortedTie.get(i).getKey()).lowestChildLevel - DR.get(sortedTie.get(i).getKey()).level;
            sortedTie.get(i).setValue(difference);
        }
        sortedTie.sort(Comparator.comparing(Map.Entry::getValue));

        Set<Integer> tie2 = new HashSet<>();
        for(int i = 0; i < sortedTie.size(); i++){
            if(sortedTie.get(i) != sortedTie.get(0))
                break;
            tie2.add(sortedTie.get(i).getKey());
        }

        int maxLevel = Integer.MIN_VALUE;
        for(int i: tie2){
            if(maxLevel < tie.get(i)) {
                maxLevel = tie.get(i);
                ret = i;
            }
        }
        return ret;
    }

    private void reSet() {
        this.DR.clear();
        this.ddr = 0;
        this.drReceivedCount = 0;
    }

    private void propagateSepDegree(int cc) {
        Set<Integer> RSep = new HashSet<>(this.sep);
        RSep.removeAll(this.CCList);
        if(RSep.size() > K ){
            for(int i : RSep){
                if(this.DR.containsKey(i)){
                    this.DR.get(i).degree++;
                }else{
                    this.DR.put(i, new DRInfo(sepLevel.get(i),1,this.level,domain.length));
                }
            }
        }
        if( this.DR.containsKey(this.id)){
            Set<Integer> DRDesc = new HashSet<>(this.DR.keySet());
            for(int i: this.DR.keySet()){
                if(this.sep.contains(i)){
                    DRDesc.remove(i);
                }
            }
            DRDesc.remove(this.id);
            if(this.DR.get(this.id).degree > this.ddr){
                this.ddr = this.DR.get(this.id).degree;
                for(int i : DRDesc){
                    this.DR.remove(i);
                }
            }else{
                this.DR.remove(this.id);
                int maxDegree = Integer.MIN_VALUE;
                int chooseOne = -1;
                for(int i : DRDesc){
                    if(maxDegree < this.DR.get(i).degree) {
                        maxDegree = this.DR.get(i).degree;
                        chooseOne = i;
                    }
                }
                for(int i : DRDesc){
                    if(i != chooseOne)
                        this.DR.remove(i);
                }
            }
        }
        sendMessage(new Message(this.id, this.parent,MSG_SEP_DEGREE ,new SepDegreeInfo(DR,ddr,cc)));
    }
    private class SepDegreeInfo{
        Map<Integer,DRInfo> sendDR;
        int sendddr;
        int cc;

        SepDegreeInfo(Map<Integer,DRInfo> DR,int sendddr, int cc){
            this.sendDR = new HashMap<>(DR);
            this.sendddr = sendddr;
            this.cc = cc;
        }
    }
    private class DRInfo{
        int level;
        int degree;
        int lowestChildLevel;
        int domainLength;

        public DRInfo(int level, int degree, int lowestChildLevel, int domainLength) {
            this.level = level;
            this.degree = degree;
            this.lowestChildLevel = lowestChildLevel;
            this.domainLength = domainLength;
        }
    }

    private NDimData boundedInference(){
        List<NDimData> utilities = new ArrayList<>();
        for (int id : this.localUtilities.keySet()){
            NDimData data = this.localUtilities.get(id);
            if (this.context.containsKey(id) || this.context.containsKey(this.id)){
                data = data.restrict(this.context);
            }
            utilities.add(data);
        }
        for(NDimData data: normalUtilities){
            for (int id : data.orderedId){ // this.id must in orderedId
                if (this.context.containsKey(id)){
                    data = data.restrict(this.context);
                    break;
                }
            }
            utilities.add(data);
        }
        for (NDimData utility : this.childrenUtilities.values()){
            NDimData data = utility;
            for (int id : utility.orderedId){ // this.id must in orderedId
                if (this.context.containsKey(id)){
                    data = data.restrict(this.context);
                    break;
                }
            }
            utilities.add(data);
        }
        if (this.context.containsKey(this.id)){
            NDimData result = NDimData.merge(utilities);
            return result;
        }
        NDimData res = NDimData.eliminate(utilities, this.id);
        return res;
    }

    private void propagateContext() {
        if (this.nodeType == NodeType.CLUSTER_ROOT) {
            if (this.searchSpace == null) {
                this.context = new HashMap<>();
                Map<Integer, Integer> domainLength = new HashMap<>(this.ccDomainLength);
                for(int cc : ccDomainLength.keySet()){
                    if(!sep.contains(cc) && cc != this.id){
                        domainLength.remove(cc);
                    }
                }
                this.searchSpace = new SearchSpace(domainLength);
            }
            this.context.clear();
            this.context.putAll(searchSpace.retrieve());
        }
        if (isCCNode()){
            this.context.put(this.id, this.curVal);
        }
        if(lastContext2child == null){
            this.lastContext2child = new HashMap<>();
            for (int c : this.childrenCCList.keySet()){
                lastContext2child.put(c,new HashMap<>());
            }
        }
        for (int c : this.childrenCCList.keySet()){
            Map<Integer, Integer> assign = new HashMap<>();
            for (int id : this.childrenCCList.get(c)){
                if(context.containsKey(id))
                    assign.put(id, this.context.get(id));
            }
            assert assign.size() != 0;
            if(contextEqual(lastContext2child.get(c),assign))
                continue;

            lastContext2child.put(c,assign);
            childrenUtilities.remove(c);
            sendMessage(new Message(this.id, c, MSG_CONTEXT, assign));
        }
        if(normalUtilityReady() && boundedUtilityReady()){
            NDimData res = boundedInference();
            sendMessage(new Message(this.id, this.parent, MSG_UTIL, res));
        }
    }
    private  boolean contextEqual(Map<Integer,Integer> pre,Map<Integer,Integer> now){
        for(int i : now.keySet()){
            if(!pre.containsKey(i))
                return false;
            else if (now.get(i).intValue() != pre.get(i))
                return false;
        }
        return  true;
    }
    private void updateNcheckVal() {
        List<NDimData> utilities = new ArrayList<>();
        for (int id : this.localUtilities.keySet()){
            NDimData data = this.localUtilities.get(id);
            if (this.context.containsKey(id) || this.context.containsKey(this.id)) {
                data = data.restrict(this.context);
            }
            utilities.add(data);
        }
        for(NDimData data: normalUtilities){
            for (int id : data.orderedId){ // this.id must in orderedId
                if (this.context.containsKey(id)){
                    data = data.restrict(this.context);
                    break;
                }
            }
            utilities.add(data);
        }
        for (NDimData utility : this.childrenUtilities.values()){
            NDimData data = utility;
            for (int id : utility.orderedId){ // this.id must in orderedId
                if (this.context.containsKey(id)){
                    data = data.restrict(this.context);
                    break;
                }
            }
            utilities.add(data);
        }
        sepCache.update(utilities, this.id, this.curVal);
        if(++curVal < domain.length){
            propagateContext();
        }else {
            curVal = 0;
            NDimData res = this.sepCache.copy();
            sendMessage(new Message(this.id, this.parent, MSG_UTIL, res));
        }
        childrenUtilities.clear();
    }

    private boolean normalUtilityReady() {
        return this.children.size() - this.childrenCCList.size() == this.numNormalUtilityReceived;
    }

    private boolean boundedUtilityReady(){
        return this.childrenUtilities.size() == this.childrenCCList.size();
    }

    private static class SepInfo {
        Map<Integer, Integer> sepDomainLength;
        Map<Integer, Integer> sepLevel;

        SepInfo(Map<Integer, Integer> sepDomainLength, Map<Integer, Integer> sepLevel) {
            this.sepDomainLength = sepDomainLength;
            this.sepLevel = sepLevel;
        }
    }

    private static class NDimData {
        int[] storage;
        Map[] assignStorage;
        List<Integer> orderedId;
        Map<Integer, Integer> domainLength;
        Map<Integer, Integer> weight;

        NDimData copy(){
            NDimData nDimData = new NDimData();
            nDimData.storage = new int[this.storage.length];
            nDimData.assignStorage = new Map[this.storage.length];
            System.arraycopy(this.storage, 0, nDimData.storage, 0, this.storage.length);
            System.arraycopy(this.assignStorage, 0, nDimData.assignStorage, 0, this.storage.length);
            nDimData.orderedId = new ArrayList<>(this.orderedId);
            nDimData.domainLength = new HashMap<>(this.domainLength);
            nDimData.weight = new HashMap<>(this.weight);
            return nDimData;
        }

        int argMin(Map<Integer,Integer> assignment){
            int result = -1;
            int freeId = -1;
            for(int i: this.domainLength.keySet()){
                if(!assignment.containsKey(i)){
                    freeId = i;
                    break;
                }
            }
            int bestCost = Integer.MAX_VALUE;
            for(int i = 0; i < this.domainLength.get(freeId); i++){
                assignment.put(freeId, i);
                int cost = getValue(assignment);
                if(cost < bestCost){
                    bestCost = cost;
                    result = i;
                }
            }
            return result;
        }

        NDimData(){
        }

        NDimData(Map<Integer, Integer> domainLength) {
            this.domainLength = new HashMap<>(domainLength);
            this.orderedId = new ArrayList<>(domainLength.keySet());
            int len =  1;
            this.weight = new HashMap<>();
            for (int i = this.orderedId.size() - 1; i >= 0; i--) {
                int curId = this.orderedId.get(i);
                this.weight.put(curId, len);
                len *= domainLength.get(curId);
            }
            this.storage = new int[len];
            this.assignStorage = new Map[len];
        }

        NDimData(Map<Integer, Integer> domainLength, int initVal) {
            this(domainLength);
            Arrays.fill(this.storage, initVal);
        }

        static NDimData fromConstraint(int[][] matrix, int rowId, int colId) {
            int rowDL = matrix.length;
            int colDL = matrix[0].length;
            Map<Integer, Integer> domainLength = new HashMap<>();
            domainLength.put(rowId, rowDL);
            domainLength.put(colId, colDL);
            NDimData data = new NDimData(domainLength);
            Map<Integer, Integer> assignment = new HashMap<>();
            for (int rowVal = 0; rowVal < rowDL; rowVal++) {
                assignment.put(rowId, rowVal);
                for (int colVal = 0; colVal < colDL; colVal++) {
                    assignment.put(colId, colVal);
                    data.setValue(assignment, matrix[rowVal][colVal]);
                }
            }
            return data;
        }

        int getIndex(Map<Integer, Integer> assignment) {
            int idx = 0;
            for (int id : this.orderedId) {
                idx += this.weight.get(id) * assignment.get(id);
            }
            return idx;
        }

        int getValue(Map<Integer, Integer> assignment) {
            return this.storage[getIndex(assignment)];
        }

        void setValue(Map<Integer, Integer> assignment, int val) {
            this.storage[getIndex(assignment)] = val;
        }

        NDimData restrict(Map<Integer, Integer> assignment){
            Map<Integer, Integer> domainLength = new HashMap<>(this.domainLength);
            for(int d: this.domainLength.keySet()){
                if(assignment.containsKey(d))
                    domainLength.remove(d);
            }
            if (domainLength.size() == 0){
                NDimData data = new NDimData();
                data.storage = new int[]{getValue(assignment)};
                data.assignStorage = new Map[]{this.assignStorage[getIndex(assignment)]};
                data.orderedId = new ArrayList<>();
                data.weight = new HashMap<>();
                data.domainLength = new HashMap<>();
                return data;
            }
            SearchSpace searchSpace = new SearchSpace(domainLength);
            NDimData result = new NDimData(domainLength);
            while (searchSpace.hasNext()) {
                Map<Integer, Integer> step = searchSpace.retrieve();
                step.putAll(assignment);
                result.setValue(step, getValue(step));
                result.assignStorage[result.getIndex(step)] = this.assignStorage[getIndex(step)];
                searchSpace.next();
            }
            return result;
        }

        NDimData eliminate(int target) {
            List<NDimData> data = new ArrayList<>();
            data.add(this);
            return eliminate(data, target);
        }

        static NDimData merge(List<NDimData> allData) {
            assert allData.size() > 1;
            Map<Integer, Integer> domainLength = new HashMap<>();
            for (NDimData data : allData) {
                domainLength.putAll(data.domainLength);
            }
            Map<Integer,Integer> mergeAssign = new HashMap<>();
            if (domainLength.size() == 0){
                NDimData data = new NDimData();
                int sum = 0;
                for (NDimData nDimData : allData){
                    sum += nDimData.storage[0];
                    mergeAssign.putAll(nDimData.assignStorage[0]);
                }
                data.storage = new int[]{sum};
                data.assignStorage = new Map[]{mergeAssign};
                data.orderedId = new ArrayList<>();
                data.weight = new HashMap<>();
                data.domainLength = new HashMap<>();
                return data;
            }
            NDimData result = new NDimData(domainLength);
            SearchSpace searchSpace = new SearchSpace(domainLength);
            while (searchSpace.hasNext()) {
                Map<Integer, Integer> assignment = searchSpace.retrieve();
                int sum = 0;
                for (NDimData data : allData) {
                    sum += data.getValue(assignment);
                    if( null != data.assignStorage[data.getIndex(assignment)]){
                        mergeAssign.putAll(data.assignStorage[data.getIndex(assignment)]);
                    }
                }
                result.setValue(assignment, sum);
                result.assignStorage[result.getIndex(assignment)] = mergeAssign;
                searchSpace.next();
                mergeAssign = new HashMap<>();
            }
            return result;
        }

        static NDimData merge(NDimData... allData) {
            List<NDimData> dataList = new ArrayList<>();
            dataList.addAll(Arrays.asList(allData));
            return merge(dataList);
        }

        static NDimData eliminate(List<NDimData> allData, int target) {
            assert allData.size() > 0;
            Map<Integer, Integer> domainLength = new HashMap<>();
            for (NDimData data : allData) {
                domainLength.putAll(data.domainLength);
            }
            int targetDL = domainLength.get(target);
            domainLength.remove(target);
            if (domainLength.size() == 0){
                NDimData data = new NDimData();
                int val = Integer.MAX_VALUE;
                Map<Integer,Integer> targetAssign = new HashMap<>();
                for (int i = 0; i < targetDL; i++){
                    int sum = 0;
                    for (NDimData nDimData : allData){
                        sum += nDimData.storage[i];
                        if(nDimData.assignStorage[i] != null)
                            targetAssign.putAll(nDimData.assignStorage[i]);
                    }
                    val = Integer.min(val, sum);
                }
                data.storage = new int[]{val};
                data.assignStorage = new Map[]{targetAssign};
                data.orderedId = new ArrayList<>();
                data.weight = new HashMap<>();
                data.domainLength = new HashMap<>();
                return data;
            }
            NDimData result = new NDimData(domainLength);
            SearchSpace searchSpace = new SearchSpace(domainLength);
            while (searchSpace.hasNext()) {
                Map<Integer, Integer> assignment = searchSpace.retrieve();
                Map<Integer, Integer> targetAssign = new HashMap<>();
                int bestUtil = Integer.MAX_VALUE;
                for (int val = 0; val < targetDL; val++) {
                    assignment.put(target, val);
                    int sum = 0;
                    for (NDimData data : allData) {
                        sum += data.getValue(assignment);
                        if( null != data.assignStorage[data.getIndex(assignment)]){
                            targetAssign.putAll(data.assignStorage[data.getIndex(assignment)]);
                        }
                    }
                    bestUtil = Integer.min(bestUtil, sum);
                }
                assignment.remove(target);
                result.setValue(assignment, bestUtil);
                result.assignStorage[result.getIndex(assignment)] = targetAssign;
                searchSpace.next();
            }
            return result;
        }

        void update(List<NDimData> otherData, int id, int curVal){
            if (this.assignStorage == null)
                this.assignStorage = new Map[this.storage.length];
            SearchSpace searchSpace = new SearchSpace(this.domainLength);
            Map<Integer,Integer> assignment = new HashMap<>();
            if(domainLength.size() == 0){
                int sum = 0;
                for (NDimData data : otherData) {
                    sum += data.storage[0];
                    if(data.assignStorage[0] != null)
                        assignment.putAll(data.assignStorage[0]);
                }
                if (sum < this.storage[0]) {
                    storage[0] = sum;
                    if(assignStorage[0] == null){
                        assignStorage[0] = new HashMap();
                    }
                    assignStorage[0].putAll(assignment);
                    assignStorage[0].put(id, curVal);
                }
                return;
            }
            while(searchSpace.hasNext()){
                Map<Integer,Integer> step = searchSpace.retrieve();
                assignment = new HashMap<>();
                int sum = 0;
                for (NDimData data : otherData) {
                    sum += data.getValue(step);
                    if( null != data.assignStorage[data.getIndex(step)]){
                        assignment.putAll(data.assignStorage[data.getIndex(step)]);
                    }
                }
                if (sum < getValue(step)) {
                    setValue(step, sum);
                    int idx = getIndex(step);
                    if(assignStorage[idx] == null)
                        assignStorage[idx] = assignment;
                    else
                        assignStorage[idx].putAll(assignment);
                }
                searchSpace.next();
            }
        }

        void update(List<NDimData> otherData, Map<Integer, Integer> assignment, int selfId, int selfDomainLength) {
            if (this.assignStorage == null)
                this.assignStorage = new Map[this.storage.length];
            Map<Integer, Integer> ccSep = new HashMap<>();
            Map<Integer, Integer> ccRemain = new HashMap<>(this.domainLength);
            Map<Integer, Integer> ccCluster = new HashMap<>();
            for (int id : assignment.keySet()) {
                if (this.domainLength.containsKey(id)) {
                    ccSep.put(id, assignment.get(id));
                    ccRemain.remove(id);
                } else {
                    ccCluster.put(id, assignment.get(id));
                }
            }
            if (ccRemain.size() == 0){
                Map<Integer, Integer> step = new HashMap<>(ccSep);
                if (assignment.containsKey(selfId)) {
                    step.put(selfId, assignment.get(selfId));
                    int sum = 0;
                    for (NDimData data : otherData) {
                        sum += data.getValue(step);
                    }
                    if (sum < getValue(step)) {
                        setValue(step, sum);
                        this.assignStorage[getIndex(step)] = ccCluster;
                    }
                } else {
                    for (int i = 0; i < selfDomainLength; i++) {
                        step.put(selfId, i);
                        int sum = 0;
                        for (NDimData data : otherData) {
                            sum += data.getValue(step);
                        }
                        if (sum < getValue(step)) {
                            Map<Integer, Integer> assign = new HashMap<>(ccCluster);
                            assign.put(selfId, i);
                            setValue(step, sum);
                            this.assignStorage[getIndex(step)] = assign;
                        }
                    }
                }
                return;
            }
            SearchSpace searchSpace = new SearchSpace(ccRemain);
            while (searchSpace.hasNext()) {
                Map<Integer, Integer> step = searchSpace.retrieve();
                step.putAll(ccSep);
                if (assignment.containsKey(selfId)) {
                    step.put(selfId, assignment.get(selfId));
                    int sum = 0;
                    for (NDimData data : otherData) {
                        sum += data.getValue(step);
                    }
                    if (sum < getValue(step)) {
                        setValue(step, sum);
                        this.assignStorage[getIndex(step)] = ccCluster;
                    }
                } else {
                    for (int i = 0; i < selfDomainLength; i++) {
                        step.put(selfId, i);
                        int sum = 0;
                        for (NDimData data : otherData) {
                            sum += data.getValue(step);
                        }
                        if (sum < getValue(step)) {
                            Map<Integer, Integer> assign = new HashMap<>(ccCluster);
                            assign.put(selfId, i);
                            setValue(step, sum);
                            this.assignStorage[getIndex(step)] = assign;
                        }
                    }
                }
                searchSpace.next();
            }
        }
    }

    protected static class SearchSpace {
        Map<Integer, Integer> domainLength;
        Map<Integer, Integer> step;
        List<Integer> orderedId;

        SearchSpace(Map<Integer, Integer> domainLength, List<Integer> orderedId) {
            this.domainLength = new HashMap<>(domainLength);
            if (orderedId != null)
                this.orderedId = new ArrayList<>(orderedId);
            else
                this.orderedId = new ArrayList<>(domainLength.keySet());
            this.step = new HashMap<>();
            for (int id : this.orderedId) {
                this.step.put(id, 0);
            }
        }

        SearchSpace(Map<Integer, Integer> domainLength) {
            this(domainLength, null);
        }

        boolean hasNext() {
            if (this.step == null)
                return true;
            int firstId = this.orderedId.get(0);
            return this.step.get(firstId) < this.domainLength.get(firstId);
        }

        Map<Integer, Integer> retrieve() {
            assert hasNext();
            return new HashMap<>(this.step);
        }

        void next() {
            assert hasNext();
            boolean carry = true;
            for (int i = this.orderedId.size() - 1; i >= 0; i--) {
                int curId = this.orderedId.get(i);
                int val = this.step.get(curId);
                val++;
                if (val == domainLength.get(curId) && i != 0) {
                    val = 0;
                } else
                    carry = false;
                this.step.put(curId, val);
                if (!carry)
                    break;

            }
        }
    }


    private class DomainLength {
        int cc;
        int domainLength;

        public DomainLength(int cc, int domainLength) {
            this.cc = cc;
            this.domainLength = domainLength;
        }
    }
    @Override
    public void runFinished() {
        super.runFinished();
        ResultCycle resultCycle = new ResultCycle();
        resultCycle.setAgentValues(id,valueIndex);
        mailer.setResultCycle(id,resultCycle);
    }
}
