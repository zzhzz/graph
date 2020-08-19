import com.ibm.wala.classLoader.IField;
import com.ibm.wala.dataflow.graph.*;
import com.ibm.wala.fixpoint.BitVectorVariable;
import com.ibm.wala.fixpoint.UnaryOperator;
import com.ibm.wala.ipa.callgraph.CGNode;
import com.ibm.wala.ipa.cfg.BasicBlockInContext;
import com.ibm.wala.ipa.cfg.ExplodedInterproceduralCFG;
import com.ibm.wala.ipa.cha.IClassHierarchy;
import com.ibm.wala.ssa.IR;
import com.ibm.wala.ssa.SSAAbstractInvokeInstruction;
import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.ssa.SSAPutInstruction;
import com.ibm.wala.ssa.analysis.IExplodedBasicBlock;
import com.ibm.wala.util.CancelException;
import com.ibm.wala.util.MonitorUtil;
import com.ibm.wala.util.collections.HashMapFactory;
import com.ibm.wala.util.collections.ObjectArrayMapping;
import com.ibm.wala.util.collections.Pair;
import com.ibm.wala.util.intset.BitVector;
import com.ibm.wala.util.intset.OrdinalSetMapping;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.Map;

public class ContextInsensitiveReachingDefs {
    private final ExplodedInterproceduralCFG icfg;
    private final OrdinalSetMapping<Pair<CGNode, Integer>> putInstrNumbering;
    private final IClassHierarchy cha;
    private final Map<IField, BitVector> staticField2DefStatements = HashMapFactory.make();

    public ContextInsensitiveReachingDefs(ExplodedInterproceduralCFG icfg, IClassHierarchy cha) {
        this.icfg = icfg;
        this.cha = cha;
        this.putInstrNumbering = this.numberPutStatics();
    }

    private OrdinalSetMapping<Pair<CGNode, Integer>> numberPutStatics() {
        ArrayList<Pair<CGNode, Integer>> putInstrs = new ArrayList();
        Iterator var2 = this.icfg.getCallGraph().iterator();

        while(true) {
            CGNode node;
            IR ir;
            do {
                if (!var2.hasNext()) {
                    ObjectArrayMapping<Pair<CGNode, Integer>> result = new ObjectArrayMapping(putInstrs.toArray(new Pair[0]));
                    return result;
                }

                node = (CGNode)var2.next();
                ir = node.getIR();
            } while(ir == null);

            SSAInstruction[] instructions = ir.getInstructions();

            for(int i = 0; i < instructions.length; ++i) {
                SSAInstruction instruction = instructions[i];
                if (instruction instanceof SSAPutInstruction && ((SSAPutInstruction)instruction).isStatic()) {
                    SSAPutInstruction putInstr = (SSAPutInstruction)instruction;
                    int instrNum = putInstrs.size();
                    putInstrs.add(Pair.make(node, i));
                    IField field = this.cha.resolveField(putInstr.getDeclaredField());

                    assert field != null;

                    BitVector bv = (BitVector)this.staticField2DefStatements.get(field);
                    if (bv == null) {
                        bv = new BitVector();
                        this.staticField2DefStatements.put(field, bv);
                    }

                    bv.set(instrNum);
                }
            }
        }
    }

    public BitVectorSolver<BasicBlockInContext<IExplodedBasicBlock>> analyze() {
        BitVectorFramework<BasicBlockInContext<IExplodedBasicBlock>, Pair<CGNode, Integer>> framework = new BitVectorFramework(this.icfg, new ContextInsensitiveReachingDefs.TransferFunctions(), this.putInstrNumbering);
        BitVectorSolver solver = new BitVectorSolver(framework);

        try {
            solver.solve(null);
        } catch (CancelException var5) {
            assert false;
        }
        return solver;
    }

    public Pair<CGNode, Integer> getNodeAndInstrForNumber(int num) {
        return (Pair)this.putInstrNumbering.getMappedObject(num);
    }

    private class TransferFunctions implements ITransferFunctionProvider<BasicBlockInContext<IExplodedBasicBlock>, BitVectorVariable> {
        private TransferFunctions() {
        }

        public AbstractMeetOperator<BitVectorVariable> getMeetOperator() {
            return BitVectorUnion.instance();
        }

        public UnaryOperator<BitVectorVariable> getNodeTransferFunction(BasicBlockInContext<IExplodedBasicBlock> node) {
            IExplodedBasicBlock ebb = (IExplodedBasicBlock)node.getDelegate();
            SSAInstruction instruction = ebb.getInstruction();
            int instructionIndex = ebb.getFirstInstructionIndex();
            CGNode cgNode = node.getNode();
            if (instruction instanceof SSAPutInstruction && ((SSAPutInstruction)instruction).isStatic()) {
                SSAPutInstruction putInstr = (SSAPutInstruction)instruction;
                IField field = ContextInsensitiveReachingDefs.this.cha.resolveField(putInstr.getDeclaredField());

                assert field != null;

                BitVector kill = (BitVector) ContextInsensitiveReachingDefs.this.staticField2DefStatements.get(field);
                BitVector gen = new BitVector();
                gen.set(ContextInsensitiveReachingDefs.this.putInstrNumbering.getMappedIndex(Pair.make(cgNode, instructionIndex)));
                return new BitVectorKillGen(kill, gen);
            } else {
                return BitVectorIdentity.instance();
            }
        }

        public boolean hasEdgeTransferFunctions() {
            return true;
        }

        public boolean hasNodeTransferFunctions() {
            return true;
        }

        public UnaryOperator<BitVectorVariable> getEdgeTransferFunction(BasicBlockInContext<IExplodedBasicBlock> src, BasicBlockInContext<IExplodedBasicBlock> dst) {
            return (UnaryOperator)(this.isCallToReturnEdge(src, dst) ? BitVectorKillAll.instance() : BitVectorIdentity.instance());
        }

        private boolean isCallToReturnEdge(BasicBlockInContext<IExplodedBasicBlock> src, BasicBlockInContext<IExplodedBasicBlock> dst) {
            SSAInstruction srcInst = ((IExplodedBasicBlock)src.getDelegate()).getInstruction();
            return srcInst instanceof SSAAbstractInvokeInstruction && src.getNode().equals(dst.getNode());
        }
    }
}

