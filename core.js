// nl-core.js — pure NLHE logic, no DOM. Best-5-of-7 evaluator (you may use
// 0, 1 or 2 hole cards — the key difference from PLO's exactly-2+3 rule).
const RANKS = '23456789TJQKA';
const SUIT_LETTER = 'shdc';
const SUIT_SYM = ['♠','♥','♦','♣'];

function cardStr(c){ return RANKS[c.r] + SUIT_LETTER[c.s]; }
function parseHand(s){ // 'AsKh'
  const m={s:0,h:1,d:2,c:3}; const out=[];
  for(let i=0;i<s.length;i+=2) out.push({r:RANKS.indexOf(s[i]), s:m[s[i+1]]});
  return out;
}
function fullDeck(){ const d=[]; for(let r=0;r<13;r++) for(let s=0;s<4;s++) d.push({r,s}); return d; }
function shuffle(a){ for(let i=a.length-1;i>0;i--){ const j=(Math.random()*(i+1))|0; const t=a[i]; a[i]=a[j]; a[j]=t; } return a; }

function combos(a,k){
  const o=[];
  (function rec(start, cur){
    if(cur.length===k){ o.push(cur.slice()); return; }
    for(let i=start;i<a.length;i++){ cur.push(a[i]); rec(i+1, cur); cur.pop(); }
  })(0, []);
  return o;
}

// ---- 5-card evaluator (same proven core as the PLO trainer) ----
function eval5(c){
  const rs=c.map(x=>x.r).sort((a,b)=>b-a);
  const flush=c.every(x=>x.s===c[0].s);
  const u=[...new Set(rs)];
  let str=-1;
  if(u.length===5){
    if(u[0]-u[4]===4) str=u[0];
    else if(u[0]===12&&u[1]===3&&u[2]===2&&u[3]===1&&u[4]===0) str=3; // wheel
  }
  const cnt={}; rs.forEach(r=>cnt[r]=(cnt[r]||0)+1);
  const g=Object.keys(cnt).map(r=>({r:+r,n:cnt[r]})).sort((a,b)=>b.n-a.n||b.r-a.r);
  const kicker=g.slice(1).map(x=>x.r);
  let cat,tb;
  if(flush&&str>=0){cat=8;tb=[str];}
  else if(g[0].n===4){cat=7;tb=[g[0].r].concat(kicker);}
  else if(g[0].n===3&&g[1].n===2){cat=6;tb=[g[0].r,g[1].r];}
  else if(flush){cat=5;tb=rs;}
  else if(str>=0){cat=4;tb=[str];}
  else if(g[0].n===3){cat=3;tb=[g[0].r].concat(kicker);}
  else if(g[0].n===2&&g[1].n===2){cat=2;tb=[g[0].r,g[1].r].concat(kicker);}
  else if(g[0].n===2){cat=1;tb=[g[0].r].concat(kicker);}
  else{cat=0;tb=rs;}
  return {cat:cat,tb:tb};
}
function cmp5(a,b){
  if(a.cat!==b.cat) return a.cat-b.cat;
  for(let i=0;i<a.tb.length&&i<b.tb.length;i++) if(a.tb[i]!==b.tb[i]) return a.tb[i]-b.tb[i];
  return 0;
}
// Best 5-card hand from 5, 6 or 7 cards (NLHE: any 5 of hole+board).
function bestOf(cards){
  let best=null;
  for(const c5 of combos(cards,5)){
    const e=eval5(c5);
    if(!best||cmp5(e,best)>0) best=e;
  }
  return best;
}
function nlBest(hand2, board){ return bestOf(hand2.concat(board)); }
function bestOnBoard(hand2, board){ return bestOf(hand2.concat(board)); }

// Monte Carlo equity vs ONE random hand, full 5-card board.
function equityVsRandom(hero2, iters){
  const base=fullDeck().filter(c=>!hero2.some(h=>h.r===c.r&&h.s===c.s));
  let win=0,tie=0;
  for(let i=0;i<iters;i++){
    const d=base.slice();
    for(let k=0;k<7;k++){ const j=k+((Math.random()*(d.length-k))|0); const t=d[k]; d[k]=d[j]; d[j]=t; }
    const board=[d[2],d[3],d[4],d[5],d[6]];
    const a=nlBest(hero2,board), b=nlBest([d[0],d[1]],board);
    const cmp=cmp5(a,b);
    if(cmp>0)win++; else if(cmp===0)tie++;
  }
  return (win+tie/2)/iters;
}

// Exact draw outs on flop/turn: unseen cards that make a straight or flush
// (or straight flush) for hero. Brute force — can't be miscounted.
function drawOuts(hero2, board){
  if(board.length<3||board.length>4) return [];
  const used=new Set(hero2.concat(board).map(c=>c.r*4+c.s));
  const outs=[];
  for(let r=0;r<13;r++) for(let s=0;s<4;s++){
    if(used.has(r*4+s)) continue;
    const c={r,s};
    const e=bestOf(hero2.concat(board).concat([c]));
    if(e.cat===4||e.cat===5||e.cat===8) outs.push(c);
  }
  return outs;
}

function classify(h){
  const [a,b]=h.slice().sort((x,y)=>y.r-x.r);
  const parts=[];
  if(a.r===b.r) parts.push('Pair of '+RANKS[a.r]+'s');
  else{
    parts.push(RANKS[a.r]+RANKS[b.r]+(a.s===b.s?' suited':' offsuit'));
    const gap=a.r-b.r-1;
    if(gap===0) parts.push('connected');
    else if(gap===1) parts.push('1-gap');
    else if(gap===2) parts.push('2-gap');
  }
  return parts.join(', ');
}

if(typeof module!=='undefined'){
  module.exports={RANKS,SUIT_LETTER,SUIT_SYM,cardStr,parseHand,fullDeck,shuffle,
    combos,eval5,cmp5,bestOf,nlBest,bestOnBoard,equityVsRandom,drawOuts,classify};
}
