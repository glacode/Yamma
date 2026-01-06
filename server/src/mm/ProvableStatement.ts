import { BlockStatement } from "./BlockStatement";
import { MmToken } from '../grammar/MmLexer';
import { AssertionStatement } from './AssertionStatement';

// export class AxiomStatementOld extends AssertionStatementOld {
//     constructor(label: string, content: string[], disjVars: DisjVars,
//         f_hyps: FHyp[], e_hyps: EHyp[], parentBlock: BlockStatement) {
//         super(label, content, disjVars, f_hyps, e_hyps, parentBlock);
//     }
// }
//export class ProvableStatement extends AssertionStatementOld {
// constructor(label: string, content: string[], disjVars: DisjVars,
//     f_hyps: FHyp[], e_hyps: EHyp[], parentBlock: BlockStatement) {
//     super(label, content, disjVars, f_hyps, e_hyps, parentBlock);

export class ProvableStatement extends AssertionStatement {

    private _compressedProofString: string | undefined;
    private _proofTokens: MmToken[] | undefined;
    private _compressedProofLabelsTokens: MmToken[] | undefined;

    isProofVerified = false;
    isProofVerificationFailed = false;

    constructor(labelToken: MmToken, content: MmToken[], parentBlock: BlockStatement, comment?: MmToken[]) {
        super(labelToken, content, parentBlock, comment);
    }

    get proofTokens(): MmToken[] {
        if (this._proofTokens == undefined) {
            this._proofTokens = [];
            let hasProofBegun = false;
            this.Content.forEach(token => {
                if (hasProofBegun)
                    this._proofTokens!.push(token);
                if (token.value == '$=')
                    hasProofBegun = true;
            });
        }
        return this._proofTokens;
    }

    get compressedProofLabelsTokens(): MmToken[] {
        if (this.proofTokens[0].value != "(") {
            this._compressedProofLabelsTokens = [];
            throw new Error("This method should be called for compressed proofs only!");
        } else if (this._compressedProofLabelsTokens == undefined) {
            this._compressedProofLabelsTokens = [];
            let i = 1;
            while (this.proofTokens[i].value != ')' && i < this.proofTokens.length) {
                this._compressedProofLabelsTokens!.push(this.proofTokens[i]);
                i++;
            }
        }
        return this._compressedProofLabelsTokens;
    }

    //TODO1 use a private var and then proofTokens
    get Proof(): string[] {
        const proof: string[] = [];
        let hasProofBegun = false;
        this.Content.forEach(token => {
            if (hasProofBegun)
                proof.push(token.value);
            if (token.value == '$=')
                hasProofBegun = true;
        });
        return proof;
    }

    get compressedProofString(): string {
        if (this._compressedProofString == undefined) {
            const proof = this.Proof;
            const closeParenthesisIndex = proof.lastIndexOf(')');
            this._compressedProofString = "";
            if (closeParenthesisIndex != -1)
                for (let index = closeParenthesisIndex + 1; index < proof.length; index++) {
                    this._compressedProofString += proof[index];
                }
        }
        return this._compressedProofString;
    }

    get CompressedProofLabels(): string[] {
        const proofStrings: string[] = this.Proof;
        if (proofStrings[0] != "(") {
            throw new Error("This method should be called for compressed proofs only!");
        }
        const closingParIndex = this.Proof.indexOf(')');
        const proofLabels = proofStrings.slice(1, closingParIndex);
        return proofLabels;
    }

    get isUnproven() {
        return this.Proof.length == 1 && this.Proof[0] == "?";
    }

    get hasCompressedProof() {
        return this.Proof.length > 1 && this.Proof[0] == "(";
    }
}
