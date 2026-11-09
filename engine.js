// engine.js — 9-handed NLHE TOURNAMENT sparring engine.
// Hero (seat 0) vs 8 equity-driven bots. No-limit, big-blind-ante style
// (0.1bb ante per player), tournament stages with ICM-graded decisions.
// Requires core.js (globals in browser, require in node).
'use strict';
const CORE = (typeof module !== 'undefined' && module.exports) ? require('./core.js') : window;

const N = 9, SB_AMT = 0.5, BB_AMT = 1, ANTE = 0.1;
const SEAT_POS = ['BTN','SB','BB','UTG','UTG+1','MP1','MP2','HJ','CO'];
function posName(seat, button){ return SEAT_POS[(seat - button + N) % N]; }

// Tournament stages. icm = risk premium applied to CALLING OFF decisions:
// on the bubble / final table, chips lost hurt more than chips won help,
// so a call needs extra equity. Aggression (shoving first-in) is NOT taxed —
// that's the whole lesson of tournament poker.
const STAGES = {
  spots:    {label:'Weekend Spots', stack:22, players:45, paid:15, icm:0.05, note:'15 to 30bb, late position, an open in front of you and a hand that matters. Call, 3bet, shove, or fold.'},
  early:    {label:'Early',        stack:100, players:180, paid:27, icm:0.00, note:'Deep. Play poker, accumulate.'},
  middle:   {label:'Middle',       stack:40,  players:64,  paid:27, icm:0.03, note:'Antes bite. Steal, don\'t gamble.'},
  bubble:   {label:'Bubble',       stack:25,  players:29,  paid:27, icm:0.10, note:'2 off the money. Calling off is taxed — shoving isn\'t.'},
  final:    {label:'Final Table',  stack:20,  players:9,   paid:9,  icm:0.13, note:'Pay jumps every hand. ICM is the game.'},
  pushfold: {label:'Push / Fold',  stack:10,  players:16,  paid:15, icm:0.05, note:'Short-stack spots. Shove or fold, no limping.'},
};

// Weekend Spots hero filter: hands with a real decision in them.
// Pairs 55+, aces (A7o+ / any suited), K9s+ / KTo+, Q9s+ / QTo+,
// J9s / JTs, and suited connectors T9s / 98s. No random trash.
function handImportant(h){
  const a=Math.max(h[0].r,h[1].r), b=Math.min(h[0].r,h[1].r);
  const suited=h[0].s===h[1].s;
  if (h[0].r===h[1].r) return h[0].r>=3;        // pair, 55 or better
  if (a===12) return b>=5 || suited;            // ace: A7o+, any suited ace
  if (a===11) return suited ? b>=7 : b>=8;      // king: K9s+, KTo+
  if (a===10) return suited ? b>=7 : b>=8;      // queen: Q9s+, QTo+ (QJ, QT, KQ, AQ...)
  if (a===9)  return suited && b>=7;            // jack: JTs, J9s
  if (suited) return a>=8 && b>=7 && a-b<=1;    // T9s, 98s
  return false;
}

// Hero/bot equity vs nOpp random hands from this point (board 0/3/4/5 cards).
function equityVsField(hand, board, nOpp, iters){
  if (nOpp <= 0) return 1;
  const used = new Set(hand.concat(board).map(c => c.r*4+c.s));
  const base = CORE.fullDeck().filter(c => !used.has(c.r*4+c.s));
  const runN = 5 - board.length;
  let share = 0;
  for (let i=0;i<iters;i++){
    const d = base.slice();
    const need = 2*nOpp + runN;
    for (let k=0;k<need;k++){ const j=k+((Math.random()*(d.length-k))|0); const t=d[k]; d[k]=d[j]; d[j]=t; }
    const b = board.concat(d.slice(2*nOpp, 2*nOpp+runN));
    const hb = CORE.nlBest(hand, b);
    let best = hb, winners = 1, heroBest = true;
    for (let p=0;p<nOpp;p++){
      const ob = CORE.nlBest([d[2*p],d[2*p+1]], b);
      const cmp = CORE.cmp5(ob, best);
      if (cmp>0){ best=ob; winners=1; heroBest=false; }
      else if (cmp===0) winners++;
    }
    if (heroBest) share += 1/winners;
  }
  return share/iters;
}

// Postflop hand tier for bots / continue-probability. NLHE version.
function assess(hand, board, preEq){
  if (board.length === 0){
    if (preEq >= 0.64) return 'strong';
    if (preEq >= 0.56) return 'good';
    if (preEq >= 0.52) return 'marginal';
    return 'weak';
  }
  const ev = CORE.bestOnBoard(hand, board);
  const cat = ev.cat;
  const dOuts = CORE.drawOuts(hand, board).length;
  // top pair / overpair check for one-pair hands
  let strongPair = false;
  if (cat === 1){
    const boardMax = Math.max(...board.map(c=>c.r));
    if (hand[0].r === hand[1].r && hand[0].r > boardMax) strongPair = true; // overpair
    else {
      // pair rank = the rank that appears in both hole+board or twice
      const all = hand.concat(board).map(c=>c.r);
      const cnt = {}; all.forEach(r=>cnt[r]=(cnt[r]||0)+1);
      const pairRank = Math.max(...Object.keys(cnt).filter(r=>cnt[r]>=2).map(Number));
      if (pairRank >= boardMax) strongPair = true; // top pair or better kicker pair
    }
  }
  if (cat >= 3) return 'strong';                    // trips, straight, flush, full+
  if (cat === 2) return 'good';                     // two pair
  if (cat === 1 && strongPair) return dOuts>=4 ? 'strong' : 'good';
  if (dOuts >= 8) return 'good';                    // real draw (flush / OESD)
  if (cat === 1) return 'marginal';
  if (dOuts >= 4) return 'marginal';                // gutshot etc.
  return 'weak';
}

class Game {
  constructor(cb, stageKey){
    this.cb = cb;
    this.stageKey = stageKey || 'early';
    this.stage = STAGES[this.stageKey];
    this.button = (Math.random()*N)|0;
    this.heroSeat = 0;
    this.handNum = 0;
    this.handsInRun = 0;
    this.sessHands = 0; this.sessNet = 0; this.sessCost = 0; this.sessGrades = [];
    try {
      const s = JSON.parse(localStorage.getItem('nl_tourn_sess')||'null');
      if (s){ this.sessHands=s.h; this.sessNet=s.n; this.sessCost=s.c; this.sessGrades=s.g||[]; }
    } catch(e){}
    this._newRun();
  }
  saveSess(){ try{ localStorage.setItem('nl_tourn_sess', JSON.stringify({h:this.sessHands,n:this.sessNet,c:this.sessCost,g:this.sessGrades.slice(-200)})); }catch(e){} }

  _newRun(){
    const st = this.stage;
    this.stacks = new Array(N);
    this.stacks[0] = st.stack;
    for (let s=1;s<N;s++){
      const f = this.stageKey==='pushfold' ? 0.7+Math.random()*0.6 : 0.55+Math.random()*1.1;
      this.stacks[s] = Math.round(st.stack*f*10)/10;
    }
    this.playersLeft = st.players;
    this.handsInRun = 0;
  }
  setStage(key){
    this.stageKey = key; this.stage = STAGES[key];
    this._newRun();
  }

  startHand(){
    if (this.stacks[0] < BB_AMT){
      this.cb.feed(`<b>💥 You busted.</b> New tournament — ${this.stage.label} stage, ${this.stage.stack}bb stack.`);
      this._newRun();
    }
    // reseat busted opponents (someone else from the field takes the seat)
    for (let s=1;s<N;s++) if (this.stacks[s] < BB_AMT){
      this.stacks[s] = Math.round(this.stage.stack*(0.6+Math.random()*0.8)*10)/10;
      this.playersLeft = Math.max(9, this.playersLeft-1);
    }
    // blinds go up every 10 hands: everyone's bb-depth shrinks 20%
    if (this.stageKey!=='spots' && this.handsInRun > 0 && this.handsInRun % 10 === 0){
      for (let s=0;s<N;s++) this.stacks[s] = Math.max(1, Math.round(this.stacks[s]*0.8*10)/10);
      this.cb.feed(`<b>⬆ Blinds up!</b> Your stack is now ${this.stacks[0].toFixed(1)}bb effective.`);
    }
    this.handsInRun++;
    this.playersLeft = Math.max(9, this.playersLeft - ((Math.random()*3)|0));
    this.handNum++;
    this.button = (this.button+1)%N;
    const deck = CORE.shuffle(CORE.fullDeck());
    this.hole = [];
    for (let s=0;s<N;s++) this.hole.push([deck.pop(),deck.pop()]);
    this.deck = deck;
    this.board = [];
    this.street = 0;
    this.handBet = new Array(N).fill(0);
    this.streetBet = new Array(N).fill(0);
    this.folded = new Array(N).fill(false);
    this.allIn = new Array(N).fill(false);
    this.acted = new Array(N).fill(false);
    this.handDone = false;
    this.awaitingHero = false;
    this.grades = [];
    this.heroStartStack = this.stacks[0];
    this.winners = null;
    if (this.stageKey==='spots') this._rigSpots();
    // antes: 0.1bb from everyone into a dead ante pot (~1bb total, BBA-style)
    this.antePot = 0;
    for (let s=0;s<N;s++){
      const a = Math.min(ANTE, this.stacks[s]);
      this.stacks[s]-=a; this.antePot+=a;
      if (this.stacks[s]<=0.001) this.allIn[s]=true;
    }
    this.preEq = [];
    for (let s=0;s<N;s++) this.preEq.push(CORE.equityVsRandom(this.hole[s], 120));
    const sb=(this.button+1)%N, bb=(this.button+2)%N;
    this._post(sb, SB_AMT); this._post(bb, BB_AMT);
    this.currentBet = BB_AMT; this.lastRaise = BB_AMT; this.raisesThisRound = 0;
    this.actionPos = bb;
    this.cb.feed(`<b>Hand #${this.handNum}</b> — ${this.stage.label} · you are <b>${posName(0,this.button)}</b> · ${this.stacks[0].toFixed(1)}bb · ${this.playersLeft} left, ${this.stage.paid} pay`);
    this.cb.update();
  }

  // ---- Weekend Spots rigging ----
  // Hero: 15-30bb, seated late, dealt a hand that matters.
  // 80% of hands someone in front of hero gets an opening hand, so the
  // first real decision is facing an open: call, 3-bet, shove, or fold.
  _drawWhere(pred){
    for (let t=0;t<80;t++){
      const h=[this.deck.pop(), this.deck.pop()];
      if (pred(h)) return h;
      // rejected cards go back at random spots so pairs re-form differently
      this.deck.splice((Math.random()*this.deck.length)|0, 0, h[0]);
      this.deck.splice((Math.random()*this.deck.length)|0, 0, h[1]);
    }
    return [this.deck.pop(), this.deck.pop()];
  }
  _rigSpots(){
    const HERO_POS=[0,0,0,8,8,8,7,7,6,2,2,1]; // BTNx3 COx3 HJx2 MP2 BBx2 SB (SEAT_POS idx)
    const idx=HERO_POS[(Math.random()*HERO_POS.length)|0];
    this.button=(N-idx)%N;
    const hs=15+((Math.random()*31)|0)/2; // 15.0 to 30.0 in half-bb steps
    const forced=ANTE + (idx===1?SB_AMT : idx===2?BB_AMT : 0); // ante + blind about to be posted
    this.stacks[0]=hs+forced; // so the stack he plays the hand with reads exactly 15-30bb
    for (let s=1;s<N;s++) this.stacks[s]=Math.round(hs*(0.6+Math.random()*0.9)*10)/10;
    this.heroStartStack=hs+forced;
    this.hole[0]=this._drawWhere(handImportant);
    if (Math.random()<0.8){
      const order=[]; let s=(this.button+3)%N; // UTG first, up to hero
      while (s!==0){ order.push(s); s=(s+1)%N; }
      if (order.length){
        const seat=order[(Math.random()*order.length)|0];
        this.hole[seat]=this._drawWhere(h=>CORE.equityVsRandom(h,150)>=0.605);
      }
    }
  }

  _post(s, amt){
    const a = Math.min(amt, this.stacks[s]);
    this.stacks[s]-=a; this.streetBet[s]+=a; this.handBet[s]+=a;
    if (this.stacks[s]<=0.001) this.allIn[s]=true;
  }
  _pot(){ return this.handBet.reduce((a,b)=>a+b,0) + this.antePot; }
  _live(){ let n=0; for(let s=0;s<N;s++) if(!this.folded[s]) n++; return n; }
  _canAct(){ let n=0; for(let s=0;s<N;s++) if(!this.folded[s]&&!this.allIn[s]) n++; return n; }

  step(){
    if (this.handDone) return {t:'end'};
    if (this._live()<=1){ this._awardUncontested(); return {t:'end'}; }
    if (this._canAct()<=1){ this._dealOut(); this._showdown(); return {t:'end'}; }
    const s = this._nextToAct();
    if (s===-1){ this._endStreet(); return {t:'street'}; }
    if (s===this.heroSeat){
      this.awaitingHero = true;
      const a = this.legalActions(s);
      this.cb.heroTurn(a);
      return {t:'hero'};
    }
    const act = this._botAction(s);
    this._apply(s, act.type, act.to);
    return {t:'bot', seat:s, act};
  }

  _nextToAct(){
    for (let i=1;i<=N;i++){
      const s=(this.actionPos+i)%N;
      if (!this.folded[s] && !this.allIn[s] && !this.acted[s]) return s;
    }
    return -1;
  }

  legalActions(seat){
    const toCall = this.currentBet - this.streetBet[seat];
    const stack = this.stacks[seat];
    const pot = this._pot();
    const r = {toCall, stack, pot, canCheck:false, canFold:false, canCall:false, callAmt:0,
               canRaise:false, minTo:0, maxTo:0, isBet:false,
               currentBet:this.currentBet, streetBet:this.streetBet[seat]};
    if (toCall > 0.001){
      r.canFold = true; r.canCall = true; r.callAmt = Math.min(toCall, stack);
      if (stack > toCall + 0.001){
        r.canRaise = true;
        r.minTo = Math.min(this.currentBet + this.lastRaise, this.streetBet[seat]+stack);
        r.maxTo = this.streetBet[seat]+stack; // no-limit: shove is always legal
        if (r.maxTo < r.minTo) r.minTo = r.maxTo;
      }
    } else {
      r.canCheck = true; r.isBet = this.currentBet<=0.001;
      if (stack > 0.001){
        r.canRaise = true;
        const minInc = this.currentBet<=0.001 ? BB_AMT : this.lastRaise;
        r.minTo = Math.min(this.currentBet + minInc, this.streetBet[seat]+stack);
        r.maxTo = this.streetBet[seat]+stack;
        if (r.maxTo < r.minTo) r.minTo = r.maxTo;
      }
    }
    return r;
  }

  heroDo(type, to){
    if (!this.awaitingHero || this.handDone) return;
    this.awaitingHero = false;
    const snap = {
      pot:this._pot(), toCall:this.currentBet - this.streetBet[0],
      streetBet:this.streetBet[0], currentBet:this.currentBet,
      stack:this.stacks[0], minTo:0, maxTo:0,
      activeOpp:[], street:this.street,
    };
    const la = this.legalActions(0);
    snap.minTo=la.minTo; snap.maxTo=la.maxTo;
    for (let s=0;s<N;s++) if (s!==0 && !this.folded[s]) snap.activeOpp.push(s);
    if (type==='fold' && !la.canFold) return;
    if (type==='check' && !la.canCheck) return;
    if (type==='call' && !la.canCall) return;
    if ((type==='bet'||type==='raise')){
      if (!la.canRaise) return;
      to = Math.max(la.minTo, Math.min(la.maxTo, to));
    }
    this._apply(0, type, to);
    this._gradeHero(snap, type, to);
    this.cb.update();
  }

  _apply(seat, type, to){
    const toCall = this.currentBet - this.streetBet[seat];
    const label = posName(seat,this.button)+(seat===0?' (you)':'');
    if (type==='fold'){
      this.folded[seat]=true; this.acted[seat]=true;
      this.cb.feed(`${label} folds`);
    } else if (type==='check'){
      this.acted[seat]=true;
      this.cb.feed(`${label} checks`);
    } else if (type==='call'){
      const amt=Math.min(toCall, this.stacks[seat]);
      this.stacks[seat]-=amt; this.streetBet[seat]+=amt; this.handBet[seat]+=amt;
      if (this.stacks[seat]<=0.001) this.allIn[seat]=true;
      this.acted[seat]=true;
      this.cb.feed(`${label} calls ${amt.toFixed(1)}${this.allIn[seat]?' (all-in)':''}`);
    } else if (type==='bet' || type==='raise'){
      const prevBet=this.currentBet, prevRaise=this.lastRaise;
      const add=Math.min(to-this.streetBet[seat], this.stacks[seat]);
      const newTo=this.streetBet[seat]+add;
      this.stacks[seat]-=add; this.streetBet[seat]=newTo; this.handBet[seat]+=add;
      const inc=newTo-prevBet;
      this.currentBet=newTo;
      const isAll=this.stacks[seat]<=0.001;
      if (isAll) this.allIn[seat]=true;
      const fullRaise = inc>=prevRaise-0.001;
      if (fullRaise){
        this.lastRaise=inc; this.raisesThisRound++;
        for (let s=0;s<N;s++) if (s!==seat && !this.folded[s] && !this.allIn[s]) this.acted[s]=false;
      }
      this.acted[seat]=true;
      this.cb.feed(`${label} ${isAll?'shoves all-in':type+'s'} to ${newTo.toFixed(1)}`);
    }
    this.actionPos=seat;
  }

  _endStreet(){
    if (this.street>=3){ this._showdown(); return; }
    this.street++;
    const n = this.street===1?3:1;
    for (let i=0;i<n;i++) this.board.push(this.deck.pop());
    this.streetBet=new Array(N).fill(0);
    this.acted=new Array(N).fill(false);
    this.currentBet=0; this.lastRaise=BB_AMT; this.raisesThisRound=0;
    let first=-1;
    for (let i=1;i<=N;i++){ const s=(this.button+i)%N; if(!this.folded[s]&&!this.allIn[s]){first=s;break;} }
    this.actionPos = first===-1 ? this.button : (first-1+N)%N;
    const nm=['preflop','FLOP','TURN','RIVER'][this.street];
    this.cb.feed(`<b>— ${nm} —</b>`);
    this.cb.update();
  }

  _dealOut(){
    while (this.street<3){
      this.street++;
      const n=this.street===1?3:1;
      for (let i=0;i<n;i++) this.board.push(this.deck.pop());
    }
    this.cb.feed(`<b>— runout —</b>`);
  }

  _pots(){
    const levels=[...new Set(this.handBet.filter(x=>x>0.001))].sort((a,b)=>a-b);
    const pots=[]; let prev=0;
    for (const lv of levels){
      const n=this.handBet.filter(x=>x>=lv-0.001).length;
      const elig=[];
      for (let s=0;s<N;s++) if(!this.folded[s]&&this.handBet[s]>=lv-0.001) elig.push(s);
      pots.push({amount:(lv-prev)*n, elig});
      prev=lv;
    }
    if (pots.length && this.antePot>0.001) pots[0].amount += this.antePot;
    return pots;
  }

  _showdown(){
    const pots=this._pots();
    const res=[];
    for (const p of pots){
      let best=null, win=[];
      for (const s of p.elig){
        const v=CORE.bestOnBoard(this.hole[s], this.board);
        if (!best||CORE.cmp5(v,best)>0){ best=v; win=[s]; }
        else if (CORE.cmp5(v,best)===0) win.push(s);
      }
      const share=p.amount/win.length;
      for (const s of win) this.stacks[s]+=share;
      res.push({amount:p.amount, winners:win});
    }
    this.winners=res;
    this.handDone=true;
    const net=this.stacks[0]-this.heroStartStack;
    this.sessHands++; this.sessNet+=net;
    let totCost=0; for (const g of this.grades) totCost+=g.cost;
    this.sessCost+=totCost;
    this.sessGrades.push(...this.grades.map(g=>g.grade));
    this.saveSess();
    this.cb.handEnd({net, pots:res, grades:this.grades});
  }

  _awardUncontested(){
    let w=-1;
    for (let s=0;s<N;s++) if(!this.folded[s]) w=s;
    const pot=this._pot();
    this.stacks[w]+=pot;
    this.winners=[{amount:pot, winners:[w], uncontested:true}];
    this.handDone=true;
    const net=this.stacks[0]-this.heroStartStack;
    this.sessHands++; this.sessNet+=net;
    let totCost=0; for (const g of this.grades) totCost+=g.cost;
    this.sessCost+=totCost;
    this.sessGrades.push(...this.grades.map(g=>g.grade));
    this.saveSess();
    this.cb.handEnd({net, pots:this.winners, grades:this.grades, uncontested:w});
  }

  // ---- bot AI (tournament-adjusted) ----
  _botAction(seat){
    const la=this.legalActions(seat);
    const pos=posName(seat,this.button);
    const eq=this.preEq[seat];
    const effStack = this.stacks[seat] + this.streetBet[seat];
    const icmCall = this.stage.icm; // bots also tighten calling off under ICM

    if (this.street===0){
      // Facing only the blinds is NOT facing a raise: first-in is open-or-fold.
      // (The old code let bots "call" the big blind with medium hands — limping —
      // which produced nonsense action like calls with no raise in front.)
      const facingRaise = this.raisesThisRound>0 || this.currentBet > BB_AMT+0.001;
      // ---- short stack: push/fold ----
      if (effStack <= 13){
        const SHOVE_T={UTG:0.59,'UTG+1':0.585,MP1:0.575,MP2:0.565,HJ:0.56,CO:0.545,BTN:0.525,SB:0.535,BB:0.60};
        if (!facingRaise){
          if (pos==='BB') return {type:'check'};
          if (pos==='SB'){
            if (eq>=(SHOVE_T.SB||0.535) && la.canRaise) return {type:'raise', to:la.maxTo};
            if (eq>=0.54 && la.canCall) return {type:'call'}; // completing is cheap and legal
            return {type:'fold'};
          }
          if (eq>=(SHOVE_T[pos]||0.56) && la.canRaise) return {type:'raise', to:la.maxTo};
          return {type:'fold'};
        }
        const need = 0.585 + icmCall*0.5; // bubble bots need more to call off
        if (eq>=need && la.canRaise) return {type:'raise', to:la.maxTo}; // shove over
        return {type:'fold'};
      }
      // ---- normal stacks ----
      const OPEN_T={UTG:0.61,'UTG+1':0.60,MP1:0.588,MP2:0.58,HJ:0.572,CO:0.555,BTN:0.52,SB:0.53,BB:0.61};
      if (!facingRaise){
        if (pos==='BB') return {type:'check'};
        if (pos==='SB'){
          if (eq>=(OPEN_T.SB||0.53) && la.canRaise)
            return {type:'raise', to:Math.min(la.maxTo, Math.max(la.minTo, 2.5))};
          if (eq>=0.50 && la.canCall) return {type:'call'}; // complete
          return {type:'fold'};
        }
        if (eq>=(OPEN_T[pos]||0.58) && la.canRaise)
          return {type:'raise', to:Math.min(la.maxTo, Math.max(la.minTo, 2.5))};
        return {type:'fold'};
      }
      // facing a real raise
      if (eq>=0.645 && this.raisesThisRound<2 && la.canRaise)
        return {type:'raise', to:Math.min(la.maxTo, Math.max(la.minTo, this.currentBet*3))};
      const callT = 0.565 + icmCall*0.35; // tighter calls on bubble/FT
      if (eq>=callT) return {type:'call'};
      if (la.toCall<=0.06*la.pot && eq>=0.52) return {type:'call'};
      return {type:'fold'};
    }
    // ---- postflop ----
    const tier=assess(this.hole[seat], this.board, eq);
    if (la.toCall>0.001){
      const odds=la.toCall/(la.pot+la.toCall);
      const callingOff = la.callAmt >= 0.4*effStack; // tournament life on the line
      if (tier==='strong'){
        if (la.canRaise && this.raisesThisRound<2 && la.toCall<0.5*la.pot) return {type:'raise', to:Math.min(la.maxTo, Math.max(la.minTo, this.currentBet*2.5))};
        return {type:'call'};
      }
      if (tier==='good'){
        if (callingOff && icmCall>=0.08) return {type:'fold'}; // ICM fold: two pair doesn't call off on the bubble
        return {type:'call'};
      }
      if (tier==='marginal' && odds<=0.25) return {type:'call'};
      if (tier==='weak' && odds<=0.05) return {type:'call'};
      return {type:'fold'};
    }
    if (tier==='strong' && la.canRaise) return {type:'bet', to:Math.min(la.maxTo, Math.max(la.minTo, la.pot*0.75))};
    if (tier==='good' && la.canRaise) return {type:'bet', to:Math.min(la.maxTo, Math.max(la.minTo, la.pot*0.5))};
    if (tier==='marginal' && la.canRaise && Math.random()<0.18) return {type:'bet', to:Math.min(la.maxTo, Math.max(la.minTo, la.pot*0.4))}; // occasional probe
    return {type:'check'};
  }

  _contProb(seat, add, pot){
    const t=assess(this.hole[seat], this.board, this.preEq[seat]);
    let p;
    if (t==='strong') p=0.95;
    else if (t==='good') p=0.8;
    else if (t==='marginal') p= add < 0.3*pot ? 0.55 : 0.22;
    else p=0.05;
    // ICM: the field folds more to big bets on the bubble / final table
    if (this.stage.icm>=0.08 && add > 0.4*pot){
      if (t==='marginal') p*=0.6;
      else if (t==='good') p*=0.85;
    }
    return p;
  }

  _gradeHero(snap, type, to){
    const eq=equityVsField(this.hole[0], this.board, snap.activeOpp.length, 150);
    const pot=snap.pot, toCall=snap.toCall;
    const icm=this.stage.icm;
    // ICM tax: CALLING for a big chunk of your stack under payout pressure.
    // Shoving first-in / raising as the aggressor is not taxed.
    const icmTaxFor=(amt)=> (icm>0 && amt > 0.30*snap.stack) ? icm*amt : 0;
    const evAgg=(add)=>{
      const ps=snap.activeOpp.map(s=>this._contProb(s, add, pot));
      const pF=ps.reduce((a,p)=>a*(1-p),1);
      const eC=ps.reduce((a,p)=>a+p,0);
      const potIfCalled=pot+add+eC*add;
      return pF*pot+(1-pF)*(eq*potIfCalled-add);
    };
    const opts=[{kind:'fold', ev:0, to:0}];
    if (toCall<=0.001) opts.push({kind:'check', ev:eq*pot, to:0});
    else opts.push({kind:'call', ev:eq*(pot+toCall)-toCall-icmTaxFor(toCall), to:0});
    const cands=[];
    if (toCall<=0.001){
      cands.push({kind:'bet', to:Math.min(snap.maxTo, Math.max(snap.minTo, pot*0.5))});
      cands.push({kind:'bet', to:Math.min(snap.maxTo, Math.max(snap.minTo, pot))});
    } else {
      cands.push({kind:'raise', to:Math.min(snap.maxTo, Math.max(snap.minTo, snap.currentBet*2.5))});
    }
    if (snap.stack>0.001) cands.push({kind:toCall>0.001?'raise':'bet', to:snap.streetBet+snap.stack, allin:true});
    for (const c of cands){
      if (c.to<=snap.streetBet+0.001) continue;
      const add=c.to-snap.streetBet;
      opts.push({kind:c.kind+(c.allin?'(allin)':''), ev:evAgg(add), to:c.to});
    }
    const best=opts.reduce((a,b)=>b.ev>a.ev?a:b);
    let chosen, icmTax=0;
    if (type==='fold') chosen=opts[0];
    else if (type==='check') chosen=opts.find(o=>o.kind==='check');
    else if (type==='call'){ chosen=opts.find(o=>o.kind==='call'); icmTax=icmTaxFor(toCall); }
    else {
      const add=to-snap.streetBet;
      chosen={kind:type, ev:evAgg(add), to};
    }
    const cost=Math.max(0, best.ev-chosen.ev);
    const grade = cost<=0.02*pot?'A':cost<=0.05*pot?'B':cost<=0.10*pot?'C':cost<=0.20*pot?'D':'F';
    const g={grade, cost, best:best.kind.replace('(allin)',''), eq, street:this.street, icmTax};
    this.grades.push(g);
    this.cb.grade(g);
  }
}

if (typeof module!=='undefined'){ module.exports={Game, equityVsField, assess, posName, N, STAGES}; }
else { window.SparGame=Game; window.sparEngine={equityVsField, assess, posName, STAGES}; }
