/* Nadi Gudang WMS: satu mesin, dua profil (window.NADI_PROFILE = 'sme' | 'large'). Tanpa backend: data hidup di localStorage. */
(()=>{'use strict';
const P=window.NADI_PROFILE==='large'?'large':'sme',L=P==='large';
const $=s=>document.querySelector(s);
const pad=n=>String(n).padStart(2,'0'),clamp=(v,a,b)=>Math.max(a,Math.min(b,v));
const esc=s=>String(s==null?'':s).replace(/[&<>"]/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;'}[c]));
const nf=(n,d=0)=>Number(n||0).toLocaleString('id-ID',{minimumFractionDigits:d,maximumFractionDigits:d});
const rp=n=>n>=1e9?'Rp '+nf(n/1e9,1)+' M':n>=1e6?'Rp '+nf(n/1e6,1)+' jt':'Rp '+nf(n);
const DAY=864e5,HR=36e5;
const iso=d=>{d=new Date(d);return`${d.getFullYear()}-${pad(d.getMonth()+1)}-${pad(d.getDate())}T${pad(d.getHours())}:${pad(d.getMinutes())}`;};
const dfmt=d=>new Date(d).toLocaleDateString('id-ID',{day:'numeric',month:'short'});
const tfmt=d=>{d=new Date(d);return pad(d.getHours())+':'+pad(d.getMinutes());};
const dtf=d=>dfmt(d)+' '+tfmt(d);
const daysTo=d=>Math.ceil((new Date(d.length===10?d+'T23:59':d)-Date.now())/DAY);
const sum=(a,f)=>a.reduce((n,x)=>n+f(x),0);

const ZT={rak:{n:'Rak penyimpanan',store:1,multi:1},lantai:{n:'Blok lantai (bulk)',store:1,multi:1},dingin:{n:'Ruang suhu terkontrol',store:1,multi:1},
  terima:{n:'Penerimaan',store:1},kirim:{n:'Pengiriman',store:1},karantina:{n:'Karantina & retur',store:1},kemas:{n:'Area kemas'},lain:{n:'Kantor / lainnya'}};
const CATS=L?['FMCG','Elektronik','Farmasi','Suku cadang','Fashion','Kimia B3']:['Sembako','Minuman','Camilan','Kebersihan','Dingin','Bumbu'];
const COLD=['Dingin','Farmasi'];
const catCol=c=>`var(--k${(CATS.indexOf(c)%8)+1||8})`;
const OPS=['Rina','Agus','Dewi','Bayu','Sari','Joko'];
const CARRIERS=['Armada sendiri','Ekspedisi darat','Kargo udara','Kurir kota'];
const VIEWS=[['peta','Denah'],['stok','Stok'],['masuk','Masuk'],['keluar','Keluar'],['pindah','Pindah'],['opname','Opname'],...(L?[['tugas','Tugas'],['dock','Dock'],['jaringan','Jaringan']]:[]),['analitik','Analitik']];

/* ================= state ================= */
let S,ZI={},SK={},BB={},MV={};
const KEY='nadi-wms-'+P+'-v1';
let saveT=0;const saveSoon=()=>{clearTimeout(saveT);saveT=setTimeout(()=>{try{localStorage.setItem(KEY,JSON.stringify(S));}catch(e){}},250);};
const saveNow=()=>{clearTimeout(saveT);try{localStorage.setItem(KEY,JSON.stringify(S));}catch(e){}};addEventListener('pagehide',()=>{if(S)saveNow();});
function load(){try{const r=localStorage.getItem(KEY);if(r){const o=JSON.parse(r);if(o&&o.v===1&&o.profile===P)return o;}}catch(e){}return null;}
function index(){ZI={};SK={};BB={};MV={};
  for(const s of S.sites)for(const z of s.zones)ZI[z.id]={z,s};
  for(const k of S.skus)SK[k.id]=k;
  S.stock=S.stock.filter(r=>r.qty>0&&ZI[r.bin.split('.')[0]]);
  for(const r of S.stock)(BB[r.bin]=BB[r.bin]||[]).push(r);
  const lim=Date.now()-30*DAY;for(const m of S.moves){if(m.t<lim)continue;if(m.from)MV[m.from]=(MV[m.from]||0)+1;if(m.to)MV[m.to]=(MV[m.to]||0)+1;}}
const site=()=>S.sites.find(s=>s.id===S.cur)||S.sites[0];
const bz=b=>ZI[b.split('.')[0]];
const single=z=>!ZT[z.type].multi;
function binCode(b){const e=bz(b);if(!e)return'—';const[,r,c]=b.split('.');return single(e.z)?e.z.code:`${e.z.code}-${pad(+c+1)}-${+r+1}`;}
function zoneBins(z){if(!ZT[z.type].store)return[];if(single(z))return[z.id+'.0.0'];const o=[];for(let r=0;r<z.rows;r++)for(let c=0;c<z.cols;c++)o.push(`${z.id}.${r}.${c}`);return o;}
const used=b=>sum(BB[b]||[],r=>r.qty*(SK[r.sku].vol||1));
const capOf=b=>{const z=bz(b).z;return single(z)?Infinity:z.cap;};
const stg=(st,type)=>{const z=st.zones.find(z=>z.type===type);return z?z.id+'.0.0':null;};
const inSite=(r,st)=>bz(r.bin).s.id===st.id;
const pickable=r=>ZT[bz(r.bin).z.type].multi;
const onHand=(id,st)=>sum(S.stock,r=>r.sku===id&&(!st||inSite(r,st))?r.qty:0);
const onOrder=(id,st)=>sum(S.pos,p=>p.status!=='selesai'&&(!st||p.site===st.id)?sum(p.lines,l=>l.sku===id?Math.max(0,l.qty-l.recv):0):0);
const zoneFill=z=>{const bs=zoneBins(z);if(single(z)||!bs.length)return null;return sum(bs,used)/(bs.length*z.cap);};
const zoneHasStock=z=>zoneBins(z).some(b=>BB[b]);

function addStock(sku,bin,qty,lot,exp,recv){const r=S.stock.find(x=>x.sku===sku&&x.bin===bin&&x.lot===(lot||''));
  if(r)r.qty+=qty;else S.stock.push({id:S.seq++,sku,bin,qty,resv:0,lot:lot||'',exp:exp||'',recv:recv||Date.now()});}
function log(type,sku,qty,from,to,ref,note,t){S.moves.push({t:t||Date.now(),type,sku,qty,from:from||'',to:to||'',ref:ref||'',note:note||''});if(S.moves.length>4000)S.moves.splice(0,S.moves.length-4000);}
function moveStock(rec,qty,to,type,ref){qty=Math.min(qty,rec.qty);rec.qty-=qty;addStock(rec.sku,to,qty,rec.lot,rec.exp,rec.recv);log(type,rec.sku,qty,rec.bin,to,ref);return qty;}

/* Saran lokasi simpan: gabung stok sama > area kategori > bin kosong; barang dingin hanya ke ruang suhu terkontrol bila ada */
function suggest(id,qty,st,extra={},n=6){const k=SK[id],need=qty*(k.vol||1),cold=COLD.includes(k.cat),heavy=(k.vol||1)>=4,out=[];
  for(const z of st.zones){if(!ZT[z.type].multi)continue;const catOk=!z.cat||z.cat===k.cat,tempOk=cold===(z.type==='dingin'),zf=(zoneFill(z)||0)*30;
    for(const b of zoneBins(z)){const free=z.cap-used(b)-(extra[b]||0);if(free<=0)continue;const rs=BB[b]||[],same=rs.some(r=>r.sku===id);
      out.push({bin:b,free,sc:(same?-100:0)+(catOk?(z.cat?-50:-10):400)+(tempOk?0:300)+(free>=need?0:150)+(rs.length&&!same?25:0)+(z.type==='lantai'?(heavy?-70:20):0)+zf+out.length*.001,
        why:!tempOk?'suhu area tidak sesuai':!catOk?'di luar kategori area':same?'gabung dengan stok yang sama':rs.length?'bin berbagi, masih muat':'bin kosong di area '+(z.cat||'campuran')});}}
  return out.sort((a,b)=>a.sc-b.sc).slice(0,n);}

/* ---- dokumen ---- */
function mkPO(sup,siteId,eta,lines){const p={id:S.seq++,no:'PO-'+(S.n.po++),sup,site:siteId,eta,status:'pesan',t:Date.now(),lines:lines.map(l=>({sku:l.sku,qty:l.qty,recv:0}))};S.pos.push(p);return p;}
function receive(po,i,q,lot,exp){const st=S.sites.find(s=>s.id===po.site),b=stg(st,'terima');if(!b)return false;const l=po.lines[i];l.recv+=q;addStock(l.sku,b,q,lot,exp);log('terima',l.sku,q,'',b,po.no);
  if(po.lines.every(l=>l.recv>=l.qty)){po.status='selesai';po.done=Date.now();}return true;}
function mkSO(cust,siteId,due,lines){const s={id:S.seq++,no:'SO-'+(S.n.so++),cust,site:siteId,due,status:'baru',t:Date.now(),short:0,lines:lines.map(l=>({sku:l.sku,qty:l.qty,alloc:[]}))};S.sos.push(s);return s;}
/* Alokasi FEFO: lot dengan kedaluwarsa terdekat dulu, lalu yang paling lama diterima; lot kedaluwarsa dilewati */
function allocate(so){let short=0;for(const ln of so.lines){let need=ln.qty-sum(ln.alloc,a=>a.qty);if(need<=0)continue;
    const recs=S.stock.filter(r=>r.sku===ln.sku&&bz(r.bin).s.id===so.site&&pickable(r)&&r.qty-r.resv>0&&!(r.exp&&daysTo(r.exp)<0)).sort((a,b)=>(a.exp||'9999').localeCompare(b.exp||'9999')||a.recv-b.recv);
    for(const r of recs){if(need<=0)break;const q=Math.min(need,r.qty-r.resv);r.resv+=q;ln.alloc.push({rec:r.id,bin:r.bin,lot:r.lot,qty:q,done:false});need-=q;}short+=need;}
  so.short=short;so.status='alokasi';}
function pickAlloc(so,a,ln){const st=S.sites.find(s=>s.id===so.site),out=stg(st,'kirim'),r=S.stock.find(x=>x.id===a.rec);if(!out||!r)return false;
  r.resv=Math.max(0,r.resv-a.qty);const q=moveStock(r,a.qty,out,'pick',so.no);a.qty=q;a.done=true;a.sku=ln.sku;
  if(so.lines.every(l=>l.alloc.every(x=>x.done)))so.status='pick';return true;}
function ship(so,carrier){const st=S.sites.find(s=>s.id===so.site),out=stg(st,'kirim');
  for(const ln of so.lines)for(const a of ln.alloc){const r=S.stock.find(x=>x.bin===out&&x.sku===ln.sku&&x.lot===a.lot);if(r){const q=Math.min(r.qty,a.qty);r.qty-=q;log('kirim',ln.sku,q,out,'',so.no);}}
  so.status='kirim';so.carrier=carrier||'';so.done=Date.now();}
function cancelSO(so){for(const ln of so.lines)for(const a of ln.alloc)if(!a.done){const r=S.stock.find(x=>x.id===a.rec);if(r)r.resv=Math.max(0,r.resv-a.qty);}S.sos.splice(S.sos.indexOf(so),1);}
function pickSteps(orders){const steps=[];for(const so of orders)for(const ln of so.lines)for(const a of ln.alloc)if(!a.done)steps.push({so,ln,a});
  if(!steps.length)return steps;const st=S.sites.find(s=>s.id===orders[0].site),z0=st.zones.find(z=>z.type==='kemas')||st.zones.find(z=>z.type==='kirim');
  let cur=z0?[z0.x+z0.w/2,z0.y+z0.h/2]:[0,0];const out=[],left=steps.slice();
  while(left.length){let bi=0,bd=1e9;left.forEach((s,i)=>{const c=binCenter(s.a.bin),d=Math.abs(c[0]-cur[0])+Math.abs(c[1]-cur[1]);if(d<bd){bd=d;bi=i;}});const s=left.splice(bi,1)[0];cur=binCenter(s.a.bin);out.push(s);}
  out.start=z0?[z0.x+z0.w/2,z0.y+z0.h/2]:null;return out;}

/* ================= data contoh ================= */
function rng(a){return()=>{a|=0;a=a+0x6D2B79F5|0;let t=Math.imul(a^a>>>15,1|a);t=t+Math.imul(t^t>>>7,61|t)^t;return((t^t>>>14)>>>0)/4294967296;};}
function seed(){const R=rng(L?77:42),ri=(a,b)=>Math.floor(a+R()*(b-a+1)),pk=a=>a[Math.floor(R()*a.length)];
  S={v:1,profile:P,seq:1,n:{po:1041,so:5120,x:210,c:31,w:12},company:L?'PT Nusantara Distribusi':'UD Sumber Rejeki',sites:[],skus:[],stock:[],pos:[],sos:[],xfers:[],counts:[],moves:[],assign:{},lastCount:{},acc:[],cur:''};
  const Z=(type,code,name,x,y,w,h,o)=>Object.assign({id:'z'+S.seq++,type,code,name,x,y,w,h,cols:1,rows:1,cap:120,cat:''},o);
  if(!L){S.sites.push({id:'s1',name:'Gudang Utama',city:'Sidoarjo',w:46,h:28,doors:[1,1],zones:[
    Z('terima','IN','Penerimaan',1,1,8,8),Z('karantina','QR','Karantina & retur',1,10,8,6),Z('kemas','PK','Meja kemas',1,17,8,4),Z('kirim','OUT','Pengiriman',1,22,8,5),
    Z('rak','A','Sembako',11,1,16,6,{cols:8,rows:2,cat:'Sembako'}),Z('rak','B','Minuman',11,8,16,6,{cols:8,rows:2,cat:'Minuman'}),
    Z('rak','C','Camilan',11,15,16,6,{cols:8,rows:2,cat:'Camilan'}),Z('rak','D','Bumbu',11,22,16,5,{cols:8,rows:2,cat:'Bumbu'}),
    Z('rak','E','Kebersihan',29,1,16,8,{cols:6,rows:3,cat:'Kebersihan'}),Z('lantai','G','Karung & dus besar',29,10,9,9,{cols:3,rows:3,cap:400}),
    Z('dingin','K','Chiller & freezer',39,10,6,9,{cols:2,rows:4,cap:80,cat:'Dingin'}),Z('lain','KT','Kantor',29,20,16,7)]});
    const D=[['Sembako','Beras premium 5 kg','karung',68000,4],['Sembako','Beras medium 25 kg','karung',310000,10],['Sembako','Gula pasir 1 kg','pak',17500,1],['Sembako','Minyak goreng 2 L','pouch',36000,2],['Sembako','Tepung terigu 1 kg','pak',13000,1],['Sembako','Mi instan goreng','dus',115000,3],['Sembako','Mi instan kuah','dus',108000,3],
      ['Minuman','Air mineral 600 ml','dus',48000,3],['Minuman','Air mineral 1,5 L','dus',52000,4],['Minuman','Teh botol 350 ml','dus',78000,3],['Minuman','Kopi sachet','renceng',14000,1],['Minuman','Susu UHT 1 L','dus',192000,3],['Minuman','Sirup 460 ml','botol',21000,1],
      ['Camilan','Biskuit kelapa','pak',9500,1],['Camilan','Keripik singkong','pak',12000,1],['Camilan','Wafer cokelat','dus',64000,2],['Camilan','Kacang kulit','pak',15000,1],['Camilan','Permen mint','toples',23000,1],
      ['Kebersihan','Sabun mandi batang','pak',18000,1],['Kebersihan','Deterjen bubuk 800 g','pak',24000,1],['Kebersihan','Sabun cuci piring 750 ml','pouch',16000,1],['Kebersihan','Pewangi pakaian 800 ml','pouch',15000,1],['Kebersihan','Tisu wajah 250 lembar','pak',11000,1],['Kebersihan','Pembersih lantai 800 ml','pouch',14000,1],
      ['Dingin','Sosis ayam beku 500 g','pak',32000,1],['Dingin','Nugget ayam 500 g','pak',41000,1],['Dingin','Es krim cup','dus',96000,2],['Dingin','Yoghurt 100 ml','pak',28000,1],['Dingin','Mentega 200 g','pak',13500,1],
      ['Bumbu','Kecap manis 520 ml','botol',22000,1],['Bumbu','Saus sambal 335 ml','botol',13000,1],['Bumbu','Garam halus 500 g','pak',5500,1],['Bumbu','Kaldu bubuk','renceng',9000,1],['Bumbu','Santan instan 65 ml','dus',98000,2]];
    const sups={Sembako:'CV Tani Makmur',Minuman:'PT Sinar Pangan',Camilan:'PT Sinar Pangan',Kebersihan:'UD Berkah Jaya',Dingin:'PT Segar Dingin',Bumbu:'UD Berkah Jaya'};
    D.forEach(([cat,name,uom,price,vol],i)=>{const min=ri(20,70);S.skus.push({id:S.seq++,code:cat.slice(0,3).toUpperCase()+'-'+pad(i+1),name,cat,uom,price,vol,min,max:min*4,lot:cat!=='Kebersihan',sup:sups[cat]});});
  }else{
    S.sites.push({id:'s1',name:'DC Cikarang',city:'Bekasi',w:84,h:46,doors:[3,3],zones:[
      Z('terima','IN','Penerimaan',1,1,11,13),Z('karantina','QC','QC & karantina',1,15,11,8),Z('kemas','PK','Kemas',1,24,11,8),Z('kirim','OUT','Pengiriman',1,33,11,12),
      Z('rak','A','FMCG cepat',14,1,22,13,{cols:10,rows:4,cap:240,cat:'FMCG'}),Z('rak','B','FMCG cadangan',38,1,22,13,{cols:10,rows:4,cap:240,cat:'FMCG'}),
      Z('rak','C','Elektronik',14,16,22,13,{cols:10,rows:4,cap:200,cat:'Elektronik'}),Z('dingin','D','Farmasi · suhu terkontrol',38,16,22,13,{cols:10,rows:4,cap:200,cat:'Farmasi'}),
      Z('rak','E','Suku cadang',14,31,22,14,{cols:10,rows:4,cap:220,cat:'Suku cadang'}),Z('rak','F','Fashion',38,31,22,14,{cols:10,rows:4,cap:260,cat:'Fashion'}),
      Z('lantai','G','Bulk & palet penuh',62,1,21,13,{cols:5,rows:3,cap:900}),Z('rak','H','Kimia B3 · berizin',62,16,21,13,{cols:7,rows:3,cap:200,cat:'Kimia B3'}),
      Z('rak','P','Pick face campuran',62,31,21,14,{cols:10,rows:4,cap:70})]});
    S.sites.push({id:'s2',name:'Hub Surabaya',city:'Surabaya',w:60,h:34,doors:[2,2],zones:[
      Z('terima','IN','Penerimaan',1,1,9,10),Z('karantina','QC','QC & karantina',1,12,9,6),Z('kemas','PK','Kemas',1,19,9,6),Z('kirim','OUT','Pengiriman',1,26,9,7),
      Z('rak','A','FMCG',12,1,22,10,{cols:8,rows:3,cap:220,cat:'FMCG'}),Z('rak','B','Elektronik',36,1,23,10,{cols:8,rows:3,cap:200,cat:'Elektronik'}),
      Z('dingin','C','Farmasi',12,13,22,9,{cols:8,rows:3,cap:200,cat:'Farmasi'}),Z('rak','D','Suku cadang',36,13,23,9,{cols:8,rows:3,cap:220,cat:'Suku cadang'}),
      Z('rak','E','Campuran',12,24,47,9,{cols:14,rows:3,cap:220})]});
    S.sites.push({id:'s3',name:'Gudang Medan',city:'Medan',w:44,h:26,doors:[1,1],zones:[
      Z('terima','IN','Penerimaan',1,1,8,8),Z('karantina','QC','Karantina',1,10,8,5),Z('kemas','PK','Kemas',1,16,8,4),Z('kirim','OUT','Pengiriman',1,21,8,4),
      Z('rak','A','FMCG',11,1,32,7,{cols:10,rows:2,cap:220,cat:'FMCG'}),Z('dingin','B','Farmasi',11,10,15,7,{cols:5,rows:2,cap:200,cat:'Farmasi'}),
      Z('rak','C','Campuran',28,10,15,7,{cols:5,rows:2,cap:240}),Z('lantai','D','Blok lantai',11,19,32,6,{cols:6,rows:1,cap:600})]});
    const G={FMCG:[['Sampo','Sabun cair','Pasta gigi','Deterjen cair','Minuman isotonik','Kopi kaleng','Sereal','Susu bubuk'],['kecil','sedang','besar'],'karton',[90,320],'PT Mitra Sejahtera Abadi'],
      Elektronik:[['Charger USB-C','Kabel HDMI','Power bank','Earphone','Lampu LED','Stopkontak','Mouse nirkabel','Router'],['A1','B2','Pro'],'unit',[45,650],'PT Elektrindo Jaya'],
      Farmasi:[['Paracetamol 500 mg','Vitamin C 500 mg','Obat batuk sirup','Antasida tablet','Salep luka','Masker medis','Sarung tangan lateks','Alkohol 70%'],['strip','box','karton'],'box',[30,420],'CV Farma Lestari'],
      'Suku cadang':[['Filter oli','Kampas rem','Busi','V-belt','Bearing 6204','Aki 12V','Lampu depan','Wiper'],['tipe S','tipe M','tipe L'],'unit',[35,900],'PT Indo Parts Prima'],
      Fashion:[['Kaos polos','Kemeja kerja','Celana chino','Jaket','Sepatu kanvas','Tas ransel'],['S','M','L'],'pcs',[60,380],'PT Garmen Nusa'],
      'Kimia B3':[['Cat tembok 5 kg','Thinner 1 L','Pelumas 4 L','Pembersih karat','Lem industri','Aerosol cat'],['A','B'],'kaleng',[40,260],'PT Kimia Andalan']};
    let i=0;for(const cat of CATS){const[bases,vars,uom,[p0,p1],sup]=G[cat];for(const b of bases)for(const v of vars){i++;const min=ri(30,120);
      S.skus.push({id:S.seq++,code:cat.replace(/[^A-Z]/gi,'').slice(0,3).toUpperCase()+'-'+String(i).padStart(3,'0'),name:b+' '+v,cat,uom,price:ri(p0,p1)*1000,vol:cat==='Fashion'||cat==='Elektronik'?1:2,min,max:min*4,lot:cat==='Farmasi'||cat==='FMCG'||cat==='Kimia B3',sup});}}
  }
  S.cur='s1';index();
  const now=Date.now(),d0=new Date();d0.setHours(0,0,0,0);
  // stok awal lewat mesin saran lokasi yang sama dengan operasional
  S.sites.forEach((st,si)=>{S.skus.forEach((k,j)=>{if(si===1&&R()>.6||si===2&&R()>.35||j%19===5)return;const low=j%7===3;
    for(let n=low?1:ri(2,4);n--;){const sg=suggest(k.id,10,st,{},3)[0];if(!sg||sg.sc>250)return;const q=Math.max(1,Math.min(Math.floor(sg.free/(k.vol||1)),low?ri(3,Math.round(k.min*.5)):ri(Math.round(k.min*.6),Math.round(k.min*2.2))));
      const e=k.lot?(R()<.05?-ri(1,6):R()<.14?ri(4,28):ri(40,420)):0,lot=k.lot?'L'+ri(2401,2612):'';
      addStock(k.id,sg.bin,q,lot,e?iso(now+e*DAY).slice(0,10):'',now-ri(1,120)*DAY);index();}});});
  for(const st of S.sites)for(const z of st.zones){if(!ZT[z.type].multi||z.cat||zoneHasStock(z))continue;const pool=S.skus.filter(k=>!COLD.includes(k.cat)&&onHand(k.id,st)>0);if(!pool.length)continue;
    for(const b of zoneBins(z)){if(R()>.62)continue;const k=pk(pool);addStock(k.id,b,Math.max(1,Math.floor(z.cap*(.35+R()*.6)/(k.vol||1))),k.lot?'L'+ri(2501,2612):'',k.lot?iso(now+ri(60,400)*DAY).slice(0,10):'',now-ri(1,60)*DAY);}index();}
  // riwayat 30 hari untuk grafik, ABC, dan lensa gerakan
  const ord=S.skus.map(k=>k.id).sort(()=>R()-.5);
  for(let d=30;d>=1;d--)for(let n=L?ri(26,40):ri(8,14);n--;){const id=ord[Math.floor(Math.pow(R(),2.4)*ord.length)],recs=S.stock.filter(r=>r.sku===id);if(!recs.length)continue;const r=pk(recs),out=R()<.68;
    log(out?'kirim':'terima',id,out?ri(2,30):ri(20,110),out?r.bin:'',out?'':r.bin,out?'SO-'+ri(4000,5100):'PO-'+ri(900,1040),'',d0.getTime()-d*DAY+ri(7,17)*HR);}
  // dokumen berjalan
  const sups=[...new Set(S.skus.map(k=>k.sup))],custs=L?['PT Ritel Maju','Apotek Sehat Group','PT Otomotif Prima','Toko Daring Gaya','PT Bangun Karya','Distributor Timur']:['Toko Bu Ani','Warung Pak Dedi','Kantin SMA 3','Minimarket Sejuk','Katering Melati'];
  const at=h=>iso(Math.round((now+h*HR)/18e5)*18e5),linesOf=(pool,n,q0,q1)=>{const s=new Set(),o=[];while(o.length<n&&s.size<pool.length){const k=pk(pool);if(s.has(k.id))continue;s.add(k.id);o.push({sku:k.id,qty:ri(q0,q1)});}return o;};
  S.sites.forEach((st,si)=>{const nP=si?2:L?6:5;
    for(let i=0;i<nP;i++){const sup=sups[(i+si)%sups.length],pool=S.skus.filter(k=>k.sup===sup),po=mkPO(sup,st.id,at([-20,-1.5,-.5,2,4.5,26][i]+si*.5),linesOf(pool,ri(2,4),30,120));
      if(i===1||i===2){po.status='tiba';po.dock=i-1;}if(i===2){receive(po,0,Math.round(po.lines[0].qty*.6),po.lines[0].sku&&SK[po.lines[0].sku].lot?'L2611':'',SK[po.lines[0].sku].lot?iso(now+200*DAY).slice(0,10):'');po.status='tiba';}}
    index();const nS=si?4:L?12:8,have=S.skus.filter(k=>onHand(k.id,st)>10);
    for(let i=0;i<nS;i++){const so=mkSO(pk(custs),st.id,at([-2,1,2,3,4,5,-1,6,8,9,24,30][i%12]),linesOf(have,ri(1,L?4:3),2,L?24:12));
      if(L&&i%3===0)so.dock=i%st.doors[1];if(i%4===1||i%4===2){allocate(so);index();}if(i%4===2&&i>2){for(const ln of so.lines)for(const a of ln.alloc)pickAlloc(so,a,ln);index();}
      if(i===6){for(const ln of so.lines)for(const a of ln.alloc)if(!a.done)pickAlloc(so,a,ln);index();if(so.status==='pick'){ship(so,pk(CARRIERS));so.done=now-3*HR;}}}
    st.zones.forEach((z,i)=>{if(ZT[z.type].multi)S.lastCount[z.id]=now-(i%3===0?44:ri(3,26))*DAY;});});
  if(L){const k=S.stock.find(r=>inSite(r,S.sites[0])&&pickable(r)&&r.qty>20);if(k){const q=Math.round(k.qty*.4);k.qty-=q;S.xfers.push({id:S.seq++,no:'TR-'+(S.n.x++),from:'s1',to:'s2',status:'transit',t:now-9*HR,items:[{sku:k.sku,qty:q,lot:k.lot,exp:k.exp}]});log('transfer',k.sku,q,k.bin,'', 'TR-209');}}
  S.acc=[98.2,97.5,99.1];index();}

/* ================= UI state ================= */
let V='peta',Q='',SEL=null,LENS='isi',EDIT=false,TOOL='sel',PEND=null,HLX=null,ROUTE=null,VB=null,DR=null,DRAW=null;
const FILT={cat:'',st:'',sort:'nama'};
const fitVB=()=>{const s=site();VB=[-1,-1,s.w+2,s.h+2];};
function toast(m,err){const el=document.createElement('div');el.className='toast'+(err?' err':'');el.textContent=m;$('#toasts').append(el);setTimeout(()=>el.remove(),err?4200:2600);}
function commit(msg){index();saveSoon();chromeBadges();refresh();if(msg)toast(msg);}

/* ================= denah ================= */
function binRect(z,r,c){const hd=1.5,x0=z.x+.3,y0=z.y+hd,iw=z.w-.6,ih=Math.max(.6,z.h-hd-.3);if(single(z))return[x0,y0,iw,ih];
  const bw=iw/z.cols,bh=ih/z.rows,g=Math.min(.12,bw*.08);return[x0+c*bw+g,y0+r*bh+g,bw-2*g,bh-2*g];}
function binCenter(b){const e=bz(b),[,r,c]=b.split('.'),q=binRect(e.z,+r,+c);return[q[0]+q[2]/2,q[1]+q[3]/2];}
let ABC=null;
function abcMap(){if(ABC)return ABC;const v={},lim=Date.now()-30*DAY;for(const m of S.moves)if(m.type==='kirim'&&m.t>=lim)v[m.sku]=(v[m.sku]||0)+m.qty*(SK[m.sku]?SK[m.sku].price:0);
  const arr=S.skus.map(k=>[k.id,v[k.id]||0]).sort((a,b)=>b[1]-a[1]),tot=sum(arr,a=>a[1])||1;let c=0;ABC={};for(const[id,x]of arr){c+=x;ABC[id]=x===0?'C':c/tot<=.8?'A':c/tot<=.95?'B':'C';}return ABC;}
const dom=rs=>rs.reduce((a,b)=>b.qty>a.qty?b:a);
function binFill(b){const rs=BB[b];if(!rs)return'var(--empty)';
  if(LENS==='isi'){const c=capOf(b),f=c===Infinity?.45:used(b)/c;return f>1?'var(--crit)':`color-mix(in srgb,var(--fill2) ${Math.round(18+clamp(f,0,1)*82)}%,var(--fill0))`;}
  if(LENS==='kat')return catCol(SK[dom(rs).sku].cat);
  if(LENS==='exp'){let d=1e9;for(const r of rs)if(r.exp)d=Math.min(d,daysTo(r.exp));return d===1e9?'var(--fill0)':d<0?'var(--crit)':d<30?'var(--warn)':d<90?'var(--mark)':'var(--ok)';}
  if(LENS==='gerak')return`color-mix(in srgb,var(--heat2) ${Math.round(clamp((MV[b]||0)/6,0,1)*100)}%,var(--fill0))`;
  return{A:'var(--k2)',B:'var(--k5)',C:'var(--k7)'}[abcMap()[dom(rs).sku]];}
function binTitle(b){const rs=BB[b]||[];return binCode(b)+(rs.length?' · '+rs.map(r=>`${r.qty} ${SK[r.sku].name}`).join(', '):' · kosong');}
function curHL(){if(ROUTE)return new Set(ROUTE.bins);if(HLX)return HLX;const q=Q.trim().toLowerCase();if(q.length<2)return null;const s=new Set();
  for(const r of S.stock){const k=SK[r.sku];if(k.name.toLowerCase().includes(q)||k.code.toLowerCase().includes(q)||binCode(r.bin).toLowerCase().startsWith(q)||r.lot.toLowerCase()===q)s.add(r.bin);}return s;}
function mapSVG(st,o={}){const hl=o.hl!==undefined?o.hl:curHL(),route=o.route!==undefined?o.route:ROUTE,vb=o.mini?[-1,-1,st.w+2,st.h+2]:VB,ed=EDIT&&!o.mini;
  let h=`<svg ${o.mini?'':'id="mapsvg"'} class="mapsvg${ed?' edit':''}" viewBox="${vb.map(v=>+v.toFixed(2)).join(' ')}" role="img" aria-label="Denah ${esc(st.name)}"><rect class="floor" x="0" y="0" width="${st.w}" height="${st.h}"/>`;
  if(ed){for(let x=2;x<st.w;x+=2)h+=`<line class="gridl" x1="${x}" y1="0" x2="${x}" y2="${st.h}"/>`;for(let y=2;y<st.h;y+=2)h+=`<line class="gridl" x1="0" y1="${y}" x2="${st.w}" y2="${y}"/>`;}
  for(const z of st.zones){const f=zoneFill(z),selz=!o.mini&&SEL&&SEL.z===z.id,name=`${z.code} · ${z.name}`,mx=Math.max(2,Math.floor(z.w*1.9)-(f==null?0:5));
    h+=`<g class="zone t-${z.type}${selz?' sel':''}" data-z="${z.id}"><rect class="zr" x="${z.x}" y="${z.y}" width="${z.w}" height="${z.h}" rx=".35"/><text class="zl" x="${z.x+.5}" y="${z.y+1.12}">${esc(name.length>mx?name.slice(0,mx-1)+'…':name)}</text>`;
    if(f!=null&&z.w>=7)h+=`<text class="zs" x="${z.x+z.w-.5}" y="${z.y+1.08}" text-anchor="end">${Math.round(f*100)}%</text>`;
    if(ZT[z.type].store){if(single(z)){const b=z.id+'.0.0',q=binRect(z,0,0),rs=BB[b]||[],n=sum(rs,r=>r.qty);
        h+=`<rect class="bin${!o.mini&&SEL&&SEL.b===b?' sel':''}${hl&&!hl.has(b)?' dim':hl?' hl':''}" data-b="${b}" x="${q[0]}" y="${q[1]}" width="${q[2]}" height="${q[3]}" rx=".2" style="fill:${rs.length?(z.type==='karantina'?'color-mix(in srgb,var(--crit) 35%,var(--fill0))':'color-mix(in srgb,var(--zc) 30%,var(--fill0))'):'var(--empty)'}"><title>${esc(binTitle(b))}</title></rect>`;
        if(q[3]>1.6)h+=`<text class="zs" x="${q[0]+q[2]/2}" y="${q[1]+q[3]/2+.3}" text-anchor="middle">${rs.length?nf(n)+' unit · '+rs.length+' lot':'kosong'}</text>`;}
      else for(let r=0;r<z.rows;r++)for(let c=0;c<z.cols;c++){const b=`${z.id}.${r}.${c}`,q=binRect(z,r,c);
        h+=`<rect class="bin${!o.mini&&SEL&&SEL.b===b?' sel':''}${hl?(hl.has(b)?' hl':' dim'):''}" data-b="${b}" x="${q[0].toFixed(2)}" y="${q[1].toFixed(2)}" width="${q[2].toFixed(2)}" height="${q[3].toFixed(2)}" rx=".12" style="fill:${binFill(b)}"><title>${esc(binTitle(b))}</title></rect>`;}}
    h+='</g>';}
  if(route&&route.site===st.id){const pts=[...(route.start?[route.start]:[]),...route.bins.map(binCenter)];h+=`<polyline class="route" points="${pts.map(p=>p.map(v=>v.toFixed(2)).join(',')).join(' ')}"/>`;
    route.bins.forEach((b,i)=>{const c=binCenter(b);h+=`<circle class="rdot" cx="${c[0]}" cy="${c[1]}" r=".8"/><text class="rnum" x="${c[0]}" y="${c[1]}">${i+1}</text>`;});}
  if(ed&&SEL&&SEL.z){const z=ZI[SEL.z]&&ZI[SEL.z].z;if(z)for(const[k,x,y]of[['nw',z.x,z.y],['ne',z.x+z.w,z.y],['sw',z.x,z.y+z.h],['se',z.x+z.w,z.y+z.h]])h+=`<rect class="hd" data-h="${k}" x="${x-.6}" y="${y-.6}" width="1.2" height="1.2"/>`;}
  if(ed&&DRAW)h+=`<rect class="draw${DRAW.ok?'':' bad'}" x="${DRAW.x}" y="${DRAW.y}" width="${DRAW.w}" height="${DRAW.h}"/>`;
  return h+'</svg>';}
const redrawMap=()=>{const w=$('#mapwrap');if(w)w.innerHTML=mapSVG(site());};
function okZone(z,st){if(z.w<3||z.h<3||z.x<0||z.y<0||z.x+z.w>st.w||z.y+z.h>st.h)return false;
  return!st.zones.some(o=>o.id!==z.id&&z.x<o.x+o.w&&z.x+z.w>o.x&&z.y<o.y+o.h&&z.y+z.h>o.y);}
function svgPt(e){const svg=$('#mapsvg'),m=svg.getScreenCTM().inverse(),p=new DOMPoint(e.clientX,e.clientY).matrixTransform(m);return{x:p.x,y:p.y,k:svg.getScreenCTM().a};}
document.addEventListener('pointerdown',e=>{if(!e.target.closest||!e.target.closest('#mapsvg'))return;const p=svgPt(e),zEl=e.target.closest('[data-z]'),hEl=e.target.closest('[data-h]'),bEl=e.target.closest('[data-b]');
  if(EDIT){e.preventDefault();
    if(TOOL==='add'){DR={k:'new',x0:Math.round(p.x),y0:Math.round(p.y)};}
    else if(hEl&&SEL&&SEL.z){const z=ZI[SEL.z].z;DR={k:'rs',h:hEl.dataset.h,z,o:{x:z.x,y:z.y,w:z.w,h:z.h}};}
    else if(zEl){const z=ZI[zEl.dataset.z].z;SEL={z:z.id};DR={k:'mv',z,o:{x:z.x,y:z.y},px:p.x,py:p.y};refresh();}
    else{SEL=null;DR={k:'pan',cx:e.clientX,cy:e.clientY};refresh();}
  }else DR={k:'pan',cx:e.clientX,cy:e.clientY,sx:e.clientX,sy:e.clientY,b:bEl&&bEl.dataset.b,z:zEl&&zEl.dataset.z};});
addEventListener('pointermove',e=>{if(!DR||!$('#mapsvg'))return;const p=svgPt(e),st=site();
  if(DR.k==='pan'){const dx=e.clientX-DR.cx,dy=e.clientY-DR.cy;if(DR.sx!=null&&!DR.moved&&Math.hypot(e.clientX-DR.sx,e.clientY-DR.sy)<5)return;DR.moved=true;VB[0]-=dx/p.k;VB[1]-=dy/p.k;DR.cx=e.clientX;DR.cy=e.clientY;}
  else if(DR.k==='mv'){DR.z.x=clamp(Math.round(DR.o.x+p.x-DR.px),0,st.w-DR.z.w);DR.z.y=clamp(Math.round(DR.o.y+p.y-DR.py),0,st.h-DR.z.h);}
  else if(DR.k==='rs'){const z=DR.z,o=DR.o,x=clamp(Math.round(p.x),0,st.w),y=clamp(Math.round(p.y),0,st.h);
    if(DR.h[1]==='e')z.w=Math.max(3,x-o.x);else{const nx=Math.min(x,o.x+o.w-3);z.x=nx;z.w=o.x+o.w-nx;}
    if(DR.h[0]==='s')z.h=Math.max(3,y-o.y);else{const ny=Math.min(y,o.y+o.h-3);z.y=ny;z.h=o.y+o.h-ny;}}
  else if(DR.k==='new'){const x=clamp(Math.round(p.x),0,st.w),y=clamp(Math.round(p.y),0,st.h);DRAW={x:Math.min(x,DR.x0),y:Math.min(y,DR.y0),w:Math.abs(x-DR.x0),h:Math.abs(y-DR.y0)};DRAW.ok=okZone({id:'',...DRAW},st);}
  redrawMap();});
addEventListener('pointerup',()=>{if(!DR)return;const d=DR,st=site();DR=null;
  if(d.k==='pan'){if(!d.moved&&d.sx!=null){if(d.b&&PEND)return doMove(d.b);SEL=d.b?{b:d.b}:d.z?{z:d.z}:null;refresh();}return;}
  if(d.k==='mv'||d.k==='rs'){if(!okZone(d.z,st)){Object.assign(d.z,d.o);toast('Area bertabrakan dengan area lain atau keluar dari bangunan',1);}commit();return;}
  if(d.k==='new'){const r=DRAW;DRAW=null;if(!r||!r.ok){redrawMap();if(r)toast('Area minimal 3 × 3 dan tidak boleh menimpa area lain',1);return;}
    const codes=new Set(st.zones.map(z=>z.code));let code='';for(const c of'ABCDEFGHJKLMNPQRSTUVWXYZ')if(!codes.has(c)){code=c;break;}
    const z={id:'z'+S.seq++,type:'rak',code:code||'Z'+S.seq,name:'Area baru',x:r.x,y:r.y,w:r.w,h:r.h,cols:Math.max(1,Math.floor(r.w/2)),rows:Math.max(1,Math.floor((r.h-1.5)/2.5)),cap:120,cat:''};
    st.zones.push(z);SEL={z:z.id};TOOL='sel';commit('Area ditambahkan. Atur nama, tipe, dan kategori di panel kanan.');}});
function doMove(to){const p=PEND,r=S.stock.find(x=>x.id===p.rec);if(!r)return;if(to===r.bin)return toast('Pilih bin yang berbeda',1);
  if(!ZT[bz(to).z.type].store)return;const need=p.qty*(SK[r.sku].vol||1);if(capOf(to)-used(to)<need)return toast(`${binCode(to)} tidak muat: sisa ruang ${nf(capOf(to)-used(to))}, butuh ${nf(need)}`,1);
  moveStock(r,p.qty,to,'pindah');PEND=null;SEL={b:to};commit(`${p.qty} ${SK[r.sku].name} dipindah ke ${binCode(to)}`);}

/* ================= komponen kecil ================= */
const meter=(f,c='',mk)=>`<div class="meter ${c}"><i style="width:${clamp(f*100,0,100).toFixed(0)}%"></i>${mk!=null?`<s style="left:${clamp(mk*100,0,100).toFixed(0)}%"></s>`:''}</div>`;
const kv=rows=>`<dl class="kv">${rows.filter(Boolean).map(([a,b])=>`<dt>${a}</dt><dd>${b}</dd>`).join('')}</dl>`;
const expTag=e=>{if(!e)return'';const d=daysTo(e);return`<span class="tag ${d<0?'c':d<30?'w':d<90?'y':'g'}">${d<0?'kedaluwarsa':'exp '+dfmt(e)}</span>`;};
const stOf=(k,st)=>{const q=onHand(k.id,st);return q===0?'habis':q<k.min?'tipis':q>k.max?'lebih':'aman';};
const stTag={habis:'<span class="tag c">Habis</span>',tipis:'<span class="tag w">Menipis</span>',lebih:'<span class="tag y">Berlebih</span>',aman:''};
function alerts(st){const o=[],now=Date.now();
  for(const k of S.skus){const s=stOf(k,st);if(s==='habis'||s==='tipis'){const oo=onOrder(k.id,st);o.push({sev:s==='habis'?'crit':'warn',t:`${k.name} ${s==='habis'?'habis':'menipis'}`,m:`${onHand(k.id,st)} / min ${k.min} ${k.uom}${oo?' · '+oo+' dalam pesanan':''}`,a:'sku',id:k.id,l:'Buka'});}}
  for(const r of S.stock)if(inSite(r,st)&&r.exp){const d=daysTo(r.exp);if(d<30)o.push({sev:d<0?'crit':'warn',t:`${SK[r.sku].name} ${d<0?'sudah kedaluwarsa':'kedaluwarsa '+d+' hari lagi'}`,m:`${r.qty} di ${binCode(r.bin)} · lot ${r.lot}`,a:'selBin',id:r.bin,l:'Lihat'});}
  for(const p of S.pos)if(p.site===st.id&&p.status==='pesan'&&new Date(p.eta)<now)o.push({sev:'warn',t:`${p.no} terlambat`,m:`${p.sup} · janji ${dtf(p.eta)}`,a:'go',id:'masuk',l:'Buka'});
  for(const s of S.sos)if(s.site===st.id&&s.status!=='kirim'){if(new Date(s.due)<now)o.push({sev:'crit',t:`${s.no} lewat tenggat`,m:`${s.cust} · ${dtf(s.due)}`,a:'go',id:'keluar',l:'Buka'});if(s.short>0)o.push({sev:'warn',t:`${s.no} kurang ${s.short} unit`,m:'Stok tidak cukup saat alokasi',a:'go',id:'keluar',l:'Buka'});}
  const tb=stg(st,'terima');if(tb&&BB[tb])o.push({sev:'info',t:`${BB[tb].length} lot menunggu disimpan`,m:'Masih di area penerimaan',a:'putAll',l:'Simpan'});
  const qb=stg(st,'karantina');if(qb&&BB[qb])o.push({sev:'info',t:`${sum(BB[qb],r=>r.qty)} unit di karantina`,m:'Perlu keputusan: kembali ke rak atau dimusnahkan',a:'selBin',id:qb,l:'Lihat'});
  for(const z of st.zones)for(const b of zoneBins(z))if(!single(z)&&used(b)>z.cap)o.push({sev:'warn',t:`${binCode(b)} melebihi kapasitas`,m:`${nf(used(b))} / ${z.cap}`,a:'selBin',id:b,l:'Lihat'});
  const w={crit:0,warn:1,info:2};return o.sort((a,b)=>w[a.sev]-w[b.sev]);}
const sigHTML=a=>`<div class="sig ${a.sev}"><span class="sev">${{crit:'KRITIS',warn:'WASPADA',info:'INFO'}[a.sev]}</span><div><b>${esc(a.t)}</b><span class="muted small">${esc(a.m)}</span><div style="margin-top:4px"><button class="btn sm" data-a="${a.a}" data-id="${a.id||''}">${a.l}</button></div></div></div>`;

/* ================= tampilan ================= */
const BODY={};
BODY.peta=()=>{const st=site();if(!VB)fitVB();const recs=S.stock.filter(r=>inSite(r,st)),bins=st.zones.flatMap(z=>single(z)?[]:zoneBins(z)),cap=sum(st.zones,z=>single(z)?0:zoneBins(z).length*z.cap),
    occ=cap?sum(bins,used)/cap:0,al=alerts(st),low=S.skus.filter(k=>['habis','tipis'].includes(stOf(k,st))).length;
  const lenses=[['isi','Isi bin'],['kat','Kategori'],['exp','Kedaluwarsa'],['gerak','Gerakan 30 hari'],...(L?[['abc','Kelas ABC']]:[])];
  const leg={isi:`<span>Kosong</span><span class="g" style="background:linear-gradient(90deg,var(--empty),var(--fill0),var(--fill2))"></span><span>Penuh</span><span><i style="background:var(--crit)"></i>Melebihi kapasitas</span>`,
    kat:CATS.map(c=>`<span><i style="background:${catCol(c)}"></i>${c}</span>`).join(''),
    exp:`<span><i style="background:var(--ok)"></i>&gt; 90 hari</span><span><i style="background:var(--mark)"></i>30–90 hari</span><span><i style="background:var(--warn)"></i>&lt; 30 hari</span><span><i style="background:var(--crit)"></i>Kedaluwarsa</span><span><i style="background:var(--fill0)"></i>Tanpa tanggal</span>`,
    gerak:`<span>Diam</span><span class="g" style="background:linear-gradient(90deg,var(--fill0),var(--heat2))"></span><span>Sering disentuh</span>`,
    abc:`<span><i style="background:var(--k2)"></i>A · 80% nilai keluar</span><span><i style="background:var(--k5)"></i>B</span><span><i style="background:var(--k7)"></i>C</span>`}[LENS];
  let banner='';
  if(EDIT)banner=`<div class="banner"><b>Mode ubah denah</b><div class="chips"><button data-a="tool" data-id="sel" aria-pressed="${TOOL==='sel'}">Pilih & geser</button><button data-a="tool" data-id="add" aria-pressed="${TOOL==='add'}">Gambar area baru</button></div><span class="small muted">${TOOL==='add'?'Seret di lantai kosong untuk menggambar area.':'Seret area untuk memindah, seret sudut kuning untuk mengubah ukuran.'}</span></div>`;
  else if(PEND){const r=S.stock.find(x=>x.id===PEND.rec);banner=r?`<div class="banner"><b>Pindahkan</b><input class="inp num" style="width:84px" type="number" min="1" max="${r.qty-r.resv}" value="${PEND.qty}" data-pq aria-label="Jumlah dipindah"><span>${esc(SK[r.sku].name)} dari ${binCode(r.bin)}. Klik bin tujuan di denah.</span><button class="btn sm" data-a="mvCancel">Batal</button></div>`:'';}
  else if(ROUTE)banner=`<div class="banner"><b>Rute pick ${esc(ROUTE.label)}</b><span>${ROUTE.bins.length} titik ambil, urut dari area kemas.</span><button class="btn sm" data-a="clearHL">Tutup rute</button></div>`;
  else if(HLX)banner=`<div class="banner"><b>${HLX.size} bin disorot</b><span>${esc(HLX.label||'')}</span><button class="btn sm" data-a="clearHL">Hapus sorotan</button></div>`;
  return`<div class="stats">${[['SKU tersimpan',nf(new Set(recs.map(r=>r.sku)).size)],['Unit di gudang',nf(sum(recs,r=>r.qty))],['Nilai stok',rp(sum(recs,r=>r.qty*SK[r.sku].price))],['Okupansi rak',nf(occ*100)+'%',occ>.9?'w':''],
      ['Order terbuka',nf(S.sos.filter(s=>s.site===st.id&&s.status!=='kirim').length)],['PO berjalan',nf(S.pos.filter(p=>p.site===st.id&&p.status!=='selesai').length)],['Perlu dipesan',nf(low),low?'w':'']].map(([l,v,c])=>`<div class="stat ${c||''}"><span class="eyebrow">${l}</span><b>${v}</b></div>`).join('')}</div>
  <div class="cols"><section class="panel"><div class="ph"><h2>Denah · ${esc(st.name)}</h2><div class="chips" role="group" aria-label="Lensa denah">${lenses.map(([k,l])=>`<button data-a="lens" data-id="${k}" aria-pressed="${LENS===k}">${l}</button>`).join('')}</div>
    <button class="btn ${EDIT?'pri':''}" data-a="edit">${EDIT?'Selesai mengubah':'Ubah denah'}</button></div>${banner}
    <div class="mapbox"><div id="mapwrap">${mapSVG(st)}</div><div class="zoom"><button data-a="zoom" data-id="in" aria-label="Perbesar">+</button><button data-a="zoom" data-id="out" aria-label="Perkecil">−</button><button data-a="zoom" data-id="fit" aria-label="Tampilkan semua">FIT</button></div></div>
    <div class="legend">${leg}</div></section>
  <aside class="rail"><section class="panel"><div class="ph"><h2>${EDIT?'Properti':'Inspektur'}</h2>${SEL?'<button class="btn sm" data-a="unsel">Tutup</button>':''}</div><div class="pb">${EDIT?editPanel(st):inspector(st)}</div></section>
    ${EDIT?'':`<section class="panel"><div class="ph"><h2>Peringatan</h2><span class="muted small">${al.length} terbuka</span></div><div class="scroll"><div class="pb">${al.slice(0,40).map(sigHTML).join('')||'<span class="muted">Tidak ada peringatan. Stok dan dokumen dalam batas.</span>'}</div></div></section>`}</aside></div>`;};
function inspector(st){
  if(SEL&&SEL.b&&bz(SEL.b)){const b=SEL.b,z=bz(b).z,rs=BB[b]||[],c=capOf(b);
    return`<div><b class="num" style="font-size:19px">${binCode(b)}</b><div class="muted small">${esc(z.name)} · ${ZT[z.type].n}</div></div>${c===Infinity?'':meter(used(b)/c,used(b)>c?'c':'')+`<span class="small muted num">${nf(used(b))} / ${c} ruang terpakai</span>`}
    ${rs.map(r=>{const k=SK[r.sku],free=r.qty-r.resv;return`<div class="item"><div class="row"><i class="dot" style="background:${catCol(k.cat)}"></i><h4>${esc(k.name)}</h4></div><span class="code">${k.code}${r.lot?' · lot '+esc(r.lot):''} · masuk ${dfmt(r.recv)}</span>
      <div class="row"><b class="num">${nf(r.qty)} ${k.uom}</b>${r.resv?`<span class="tag y">${r.resv} dialokasi</span>`:''}${expTag(r.exp)}</div>
      <div class="row"><button class="btn sm" data-a="mvStart" data-id="${r.id}" ${free>0?'':'disabled'}>Pindahkan</button><button class="btn sm" data-a="adjust" data-id="${r.id}">Sesuaikan</button>${z.type!=='karantina'?`<button class="btn sm" data-a="quar" data-id="${r.id}" ${free>0?'':'disabled'}>Karantina</button>`:''}<button class="btn sm" data-a="sku" data-id="${k.id}">Barang</button></div></div>`;}).join('')||'<span class="muted">Bin kosong.</span>'}`;}
  if(SEL&&SEL.z&&ZI[SEL.z]){const z=ZI[SEL.z].z,bs=zoneBins(z),f=zoneFill(z),agg={};for(const b of bs)for(const r of BB[b]||[])agg[r.sku]=(agg[r.sku]||0)+r.qty;
    const top=Object.entries(agg).sort((a,b)=>b[1]-a[1]),mx=top.length?top[0][1]:1,lc=S.lastCount[z.id];
    return`<div><b style="font:600 19px var(--display);letter-spacing:.06em">${esc(z.code)} · ${esc(z.name)}</b><div class="muted small">${ZT[z.type].n}${z.cat?' · khusus '+esc(z.cat):ZT[z.type].multi?' · kategori campuran':''}</div></div>
    ${f!=null?meter(f,f>.9?'w':''):''}${kv([f!=null&&['Okupansi',`<span class="num">${nf(f*100)}%</span>`],ZT[z.type].multi&&['Bin',`<span class="num">${bs.filter(b=>BB[b]).length} terisi / ${bs.length}</span>`],['Jenis barang',`<span class="num">${top.length}</span> SKU`],['Total unit',`<span class="num">${nf(sum(top,t=>t[1]))}</span>`],ZT[z.type].multi&&['Opname terakhir',lc?dfmt(lc):'belum pernah']])}
    ${top.length?'<span class="eyebrow">Yang disimpan di sini</span>':''}${top.slice(0,8).map(([id,q])=>`<div class="hbar"><span>${esc(SK[id].name)}</span><span class="num">${nf(q)}</span>${meter(q/mx)}</div>`).join('')}${top.length>8?`<span class="muted small">+${top.length-8} SKU lain</span>`:''}
    <div class="row">${ZT[z.type].multi?`<button class="btn sm" data-a="cntStart" data-id="${z.id}">Opname area ini</button>`:''}${z.type==='terima'&&top.length?'<button class="btn sm pri" data-a="putAll">Simpan ke rak</button>':''}</div>`;}
  return`<span class="muted small">Klik area atau bin di denah untuk melihat isinya. Kotak kecil adalah bin; warnanya mengikuti lensa.</span><span class="eyebrow">Area di gudang ini</span>${st.zones.filter(z=>ZT[z.type].store).map(z=>{const f=zoneFill(z),n=sum(zoneBins(z),b=>sum(BB[b]||[],r=>r.qty));
    return`<button class="item" style="border:0;text-align:left" data-a="selZone" data-id="${z.id}"><div class="hbar"><span><i class="dot" style="background:${z.cat?catCol(z.cat):'var(--faint)'}"></i>${esc(z.code)} · ${esc(z.name)}</span><span class="num">${f!=null?nf(f*100)+'%':nf(n)+' unit'}</span>${f!=null?meter(f,f>.9?'w':''):''}</div></button>`;}).join('')}`;}
function editPanel(st){const fld=(l,html)=>`<label class="fld"><span>${l}</span>${html}</label>`;
  if(SEL&&SEL.z&&ZI[SEL.z]){const z=ZI[SEL.z].z,m=ZT[z.type].multi;
    return`${fld('Nama area',`<input class="inp" data-zp="name" value="${esc(z.name)}">`)}<div class="frow">${fld('Kode',`<input class="inp num" data-zp="code" maxlength="4" value="${esc(z.code)}">`)}${fld('Tipe',`<select class="inp" data-zp="type">${Object.entries(ZT).map(([k,t])=>`<option value="${k}"${k===z.type?' selected':''}>${t.n}</option>`).join('')}</select>`)}</div>
    ${m?`<div class="frow">${fld('Kolom bin',`<input class="inp num" type="number" min="1" max="40" data-zp="cols" value="${z.cols}">`)}${fld('Tingkat / baris',`<input class="inp num" type="number" min="1" max="12" data-zp="rows" value="${z.rows}">`)}${fld('Kapasitas per bin',`<input class="inp num" type="number" min="1" data-zp="cap" value="${z.cap}">`)}</div>
    ${fld('Kategori yang disimpan',`<select class="inp" data-zp="cat"><option value="">Campuran</option>${CATS.map(c=>`<option${c===z.cat?' selected':''}>${c}</option>`).join('')}</select>`)}`:''}
    <span class="small muted num">Posisi ${z.x},${z.y} · ukuran ${z.w} × ${z.h} m</span><div class="row"><button class="btn sm danger" data-a="delZone" data-id="${z.id}">Hapus area</button></div>`;}
  return`<span class="muted small">Pilih area untuk mengubahnya, atau atur bangunan di bawah.</span>${fld('Nama gudang',`<input class="inp" data-sp="name" value="${esc(st.name)}">`)}${fld('Kota',`<input class="inp" data-sp="city" value="${esc(st.city)}">`)}
    <div class="frow">${fld('Panjang (m)',`<input class="inp num" type="number" min="12" max="160" data-sp="w" value="${st.w}">`)}${fld('Lebar (m)',`<input class="inp num" type="number" min="10" max="100" data-sp="h" value="${st.h}">`)}</div>
    ${L?`<div class="row"><button class="btn sm" data-a="addSite">+ Gudang baru</button>${S.sites.length>1?'<button class="btn sm danger" data-a="delSite">Hapus gudang ini</button>':''}</div>`:''}`;}

BODY.stok=()=>{const st=site(),q=Q.trim().toLowerCase(),ab=L?abcMap():null;
  let list=S.skus.filter(k=>(!FILT.cat||k.cat===FILT.cat)&&(!q||k.name.toLowerCase().includes(q)||k.code.toLowerCase().includes(q))).map(k=>({k,oh:onHand(k.id,st),s:stOf(k,st)}));
  if(FILT.st==='exp')list=list.filter(x=>S.stock.some(r=>r.sku===x.k.id&&inSite(r,st)&&r.exp&&daysTo(r.exp)<30));else if(FILT.st)list=list.filter(x=>x.s===FILT.st||(FILT.st==='tipis'&&x.s==='habis'));
  list.sort(FILT.sort==='qty'?(a,b)=>b.oh-a.oh:FILT.sort==='nilai'?(a,b)=>b.oh*b.k.price-a.oh*a.k.price:FILT.sort==='kritis'?(a,b)=>a.oh/a.k.min-b.oh/b.k.min:(a,b)=>a.k.name.localeCompare(b.k.name));
  const low=S.skus.filter(k=>onHand(k.id,st)+onOrder(k.id,st)<k.min).length;
  return`<div class="bar"><div class="chips"><button data-a="fcat" data-id="" aria-pressed="${!FILT.cat}">Semua</button>${CATS.map(c=>`<button data-a="fcat" data-id="${c}" aria-pressed="${FILT.cat===c}"><i class="dot" style="background:${catCol(c)}"></i>${c}</button>`).join('')}</div>
    <select class="inp" data-f="st" aria-label="Status stok">${[['','Semua status'],['tipis','Menipis & habis'],['lebih','Berlebih'],['exp','Kedaluwarsa < 30 hari']].map(([v,l])=>`<option value="${v}"${FILT.st===v?' selected':''}>${l}</option>`).join('')}</select>
    <select class="inp" data-f="sort" aria-label="Urutan">${[['nama','Urut nama'],['kritis','Paling kritis'],['qty','Jumlah terbanyak'],['nilai','Nilai terbesar']].map(([v,l])=>`<option value="${v}"${FILT.sort===v?' selected':''}>${l}</option>`).join('')}</select>
    <span class="sp"></span><button class="btn" data-a="reorder">Saran pesan ulang${low?` (${low})`:''}</button><button class="btn pri" data-a="newSku">+ Barang</button></div>
  <div class="tiles">${list.map(({k,oh,s})=>{const sc=Math.max(k.max,oh,1),rv=sum(S.stock,r=>r.sku===k.id&&inSite(r,st)?r.resv:0),oo=onOrder(k.id,st),nb=new Set(S.stock.filter(r=>r.sku===k.id&&inSite(r,st)).map(r=>r.bin)).size;
    return`<button class="tile" data-a="sku" data-id="${k.id}"><div class="row"><i class="dot" style="background:${catCol(k.cat)}"></i><span class="num small muted">${k.code}</span>${ab?`<span class="tag">${ab[k.id]}</span>`:''}${stTag[s]}</div><h4>${esc(k.name)}</h4>
    <div class="q"><b>${nf(oh)}</b><span class="muted small">${k.uom} · min ${k.min} · maks ${k.max}</span></div>${meter(oh/sc,s==='habis'||s==='tipis'?'w':s==='lebih'?'y':'',k.min/sc)}
    <div class="row small muted"><span>${nb} bin</span>${rv?`<span>· ${rv} dialokasi</span>`:''}${oo?`<span>· ${oo} dipesan</span>`:''}${L?`<span>· jaringan ${nf(onHand(k.id))}</span>`:''}</div></button>`;}).join('')||'<div class="empty">Tidak ada barang yang cocok dengan filter.</div>'}</div>`;};

const lane=(t,n,cards,extra='')=>`<section class="lane"><header><h3>${t}</h3>${extra}<span>${n}</span></header><div class="cards">${cards||'<div class="empty">Kosong</div>'}</div></section>`;
const lnHTML=(ls,f)=>`<div class="lines">${ls.slice(0,4).map(l=>`<div class="ln"><span>${esc(SK[l.sku].name)}</span><span class="num">${f(l)}</span></div>`).join('')}${ls.length>4?`<span class="muted">+${ls.length-4} baris lain</span>`:''}</div>`;
BODY.masuk=()=>{const st=site(),ps=S.pos.filter(p=>p.site===st.id),tb=stg(st,'terima'),stag=tb?BB[tb]||[]:[],now=Date.now();
  const card=p=>{const late=p.status==='pesan'&&new Date(p.eta)<now,tot=sum(p.lines,l=>l.qty),rc=sum(p.lines,l=>l.recv);
    return`<div class="card"><div class="hd1"><b>${p.no}</b>${late?'<span class="tag c">Terlambat</span>':p.status==='selesai'?'<span class="tag g">Lengkap</span>':rc?'<span class="tag y">Sebagian</span>':''}</div><span>${esc(p.sup)}</span>
    <span class="small muted">${p.status==='selesai'?'Selesai '+dtf(p.done):'Tiba '+dtf(p.eta)}${p.dock!=null?' · dock masuk '+(p.dock+1):''}</span>${meter(rc/tot,'g')}${lnHTML(p.lines,l=>`${l.recv}/${l.qty}`)}
    <div class="row">${p.status==='pesan'?`<button class="btn sm pri" data-a="arrive" data-id="${p.id}">Truk tiba</button><button class="btn sm" data-a="delPO" data-id="${p.id}">Batalkan</button>`:p.status==='tiba'?`<button class="btn sm pri" data-a="receive" data-id="${p.id}">Terima barang</button>`:''}</div></div>`;};
  const by=s=>ps.filter(p=>p.status===s);
  return`<div class="bar"><span class="muted small">Alur: pesan → truk tiba → terima ke area penerimaan → simpan ke rak dengan saran lokasi.</span><span class="sp"></span><button class="btn" data-a="retur">+ Retur pelanggan</button><button class="btn pri" data-a="newPO">+ PO baru</button></div>
  <div class="board">${lane('Dipesan',by('pesan').length,by('pesan').sort((a,b)=>a.eta.localeCompare(b.eta)).map(card).join(''))}${lane('Tiba di dock',by('tiba').length,by('tiba').map(card).join(''))}
  ${lane('Menunggu disimpan',stag.length,stag.map(r=>{const k=SK[r.sku],sg=suggest(r.sku,r.qty,st,{},1)[0];return`<div class="card"><div class="hd1"><b>${nf(r.qty)} ${k.uom}</b>${expTag(r.exp)}</div><span>${esc(k.name)}</span><span class="small muted">${sg?`Saran: <span class="num">${binCode(sg.bin)}</span> · ${sg.why}`:'Tidak ada bin yang muat'}</span>
    <div class="row"><button class="btn sm pri" data-a="putOne" data-id="${r.id}" ${sg?'':'disabled'}>Simpan</button></div></div>`;}).join(''),stag.length?'<button class="btn sm" data-a="putAll">Atur semua</button>':'')}
  ${lane('Selesai',by('selesai').length,by('selesai').sort((a,b)=>b.done-a.done).slice(0,6).map(card).join(''))}</div>`;};

BODY.keluar=()=>{const st=site(),ss=S.sos.filter(s=>s.site===st.id),now=Date.now(),by=s=>ss.filter(x=>x.status===s).sort((a,b)=>a.due.localeCompare(b.due));
  const card=s=>{const late=s.status!=='kirim'&&new Date(s.due)<now,tot=sum(s.lines,l=>l.qty),al=sum(s.lines,l=>sum(l.alloc,a=>a.qty)),pk=sum(s.lines,l=>sum(l.alloc,a=>a.done?a.qty:0));
    const btn={baru:`<button class="btn sm pri" data-a="alloc" data-id="${s.id}">Alokasikan stok</button><button class="btn sm" data-a="cancelSO" data-id="${s.id}">Batalkan</button>`,
      alokasi:`<button class="btn sm pri" data-a="pick" data-id="${s.id}" ${al?'':'disabled'}>Pick</button><button class="btn sm" data-a="routeSO" data-id="${s.id}" ${al?'':'disabled'}>Rute di denah</button>${s.short?`<button class="btn sm" data-a="alloc" data-id="${s.id}">Alokasi ulang</button>`:''}<button class="btn sm" data-a="cancelSO" data-id="${s.id}">Batalkan</button>`,
      pick:L?`<button class="btn sm pri" data-a="pack" data-id="${s.id}">Kemas</button>`:`<button class="btn sm pri" data-a="ship" data-id="${s.id}">Kirim</button>`,kemas:`<button class="btn sm pri" data-a="ship" data-id="${s.id}">Muat & kirim</button>`,kirim:''}[s.status];
    return`<div class="card"><div class="hd1"><b>${s.no}</b>${late?'<span class="tag c">Lewat tenggat</span>':''}${s.short?`<span class="tag w">Kurang ${s.short}</span>`:''}${s.wave?`<span class="tag">${s.wave}</span>`:''}</div><span>${esc(s.cust)}</span>
    <span class="small muted">${s.status==='kirim'?'Terkirim '+dtf(s.done)+(s.carrier?' · '+esc(s.carrier):''):'Tenggat '+dtf(s.due)}${s.koli?' · '+s.koli+' koli':''}</span>${meter(s.status==='kirim'?1:(al+pk)/(2*tot),'y')}${lnHTML(s.lines,l=>l.qty+' '+SK[l.sku].uom)}<div class="row">${btn}</div></div>`;};
  const nA=by('alokasi').filter(s=>!s.short||sum(s.lines,l=>l.alloc.length)).length;
  return`<div class="bar"><span class="muted small">Alur: order → alokasi FEFO → pick dengan rute terpendek → ${L?'kemas → ':''}kirim.</span><span class="sp"></span>${by('baru').length>1?'<button class="btn" data-a="allocAll">Alokasikan semua</button>':''}<button class="btn pri" data-a="newSO">+ Order baru</button></div>
  <div class="board">${lane('Baru',by('baru').length,by('baru').map(card).join(''))}${lane('Dialokasi',by('alokasi').length,by('alokasi').map(card).join(''),L&&nA>1?'<button class="btn sm" data-a="wave">Pick sebagai wave</button>':'')}
  ${lane('Dipick',by('pick').length,by('pick').map(card).join(''))}${L?lane('Dikemas',by('kemas').length,by('kemas').map(card).join('')):''}${lane('Terkirim',by('kirim').length,ss.filter(s=>s.status==='kirim').sort((a,b)=>b.done-a.done).slice(0,6).map(card).join(''))}</div>`;};

const mvType={terima:['Terima','k1'],putaway:['Simpan','k4'],pick:['Pick','k5'],kirim:['Kirim','k2'],pindah:['Pindah','k3'],opname:['Opname','k7'],sesuai:['Koreksi','k6'],retur:['Retur','k6'],transfer:['Antar gudang','k3']};
const mvHTML=m=>{const[t,c]=mvType[m.type]||[m.type,'k8'],k=SK[m.sku];return`<div class="mv"><span class="t">${dfmt(m.t)} ${tfmt(m.t)}</span><span><i class="dot" style="background:var(--${c})"></i><b>${t}</b> ${m.qty>0&&(m.type==='opname'||m.type==='sesuai')?'+':''}${nf(m.qty)} × ${esc(k?k.name:'(dihapus)')}</span><span class="num muted">${m.from&&bz(m.from)?binCode(m.from):''}${m.from&&m.to?' → ':''}${m.to&&bz(m.to)?binCode(m.to):''}${m.ref?' · '+esc(m.ref):''}</span></div>`;};
const mvInSite=(m,st)=>{const b=m.to||m.from,e=b&&bz(b);return e&&e.s.id===st.id;};
BODY.pindah=()=>{const st=site(),mv=S.moves.filter(m=>['pindah','putaway','transfer'].includes(m.type)&&mvInSite(m,st)).slice(-40).reverse(),xs=S.xfers.filter(x=>x.status==='transit');
  return`<div class="bar"><span class="muted small">Cara cepat: buka Denah, klik bin, tekan Pindahkan, lalu klik bin tujuan.</span><span class="sp"></span><button class="btn pri" data-a="xfer">+ Pindahkan stok</button></div>
  ${L?`<section class="panel" style="margin-bottom:14px"><div class="ph"><h2>Antar gudang · dalam perjalanan</h2><span class="muted small">${xs.length} kiriman</span></div><div class="pb">${xs.map(xferCard).join('')||'<span class="muted">Tidak ada kiriman antar gudang yang sedang berjalan.</span>'}</div></section>`:''}
  <section class="panel"><div class="ph"><h2>Perpindahan terakhir</h2></div><div class="pb"><div class="stream">${mv.map(mvHTML).join('')||'<span class="muted">Belum ada perpindahan.</span>'}</div></div></section>`;};
const sname=id=>{const s=S.sites.find(s=>s.id===id);return s?s.name:'—';};
const xferCard=x=>`<div class="item"><div class="row"><b class="num">${x.no}</b><span>${esc(sname(x.from))} → ${esc(sname(x.to))}</span><span class="muted small">berangkat ${dtf(x.t)}</span></div>${x.items.map(i=>`<span class="small">${nf(i.qty)} × ${esc(SK[i.sku].name)}${i.lot?' · lot '+esc(i.lot):''}</span>`).join('')}<div class="row"><button class="btn sm pri" data-a="xrecv" data-id="${x.id}">Terima di ${esc(sname(x.to))}</button></div></div>`;

BODY.opname=()=>{const st=site(),c=S.counts.find(c=>c.status==='buka'&&ZI[c.zone]&&ZI[c.zone].s.id===st.id);
  if(c){const z=ZI[c.zone].z,done=c.lines.filter(l=>l.cnt!=null).length,diff=c.lines.filter(l=>l.cnt!=null&&l.cnt!==l.sys).length;
    return`<div class="bar"><b>${c.no} · ${esc(z.code)} ${esc(z.name)}</b><span class="muted small">${done}/${c.lines.length} dihitung · ${diff} selisih</span><span class="sp"></span><button class="btn" data-a="cntFill">Isi sesuai sistem</button><button class="btn" data-a="cntCancel">Batalkan</button><button class="btn pri" data-a="cntPost" ${done===c.lines.length?'':'disabled'}>Posting hasil</button></div>
    ${meter(done/Math.max(1,c.lines.length),'g')}<div class="tiles" style="margin-top:12px">${c.lines.map((l,i)=>{const k=SK[l.sku],d=l.cnt==null?null:l.cnt-l.sys;
      return`<div class="tile"><div class="row"><span class="num"><b>${binCode(l.bin)}</b></span>${d==null?'':d===0?'<span class="tag g">Cocok</span>':`<span class="tag ${d<0?'c':'w'}">${d>0?'+':''}${d}</span>`}</div><h4>${esc(k.name)}</h4><span class="small muted">${l.lot?'lot '+esc(l.lot)+' · ':''}sistem <span class="num">${l.sys}</span> ${k.uom}</span>
      <label class="fld"><span>Hasil hitung fisik</span><input class="inp num" type="number" min="0" data-cnt="${i}" value="${l.cnt==null?'':l.cnt}"></label></div>`;}).join('')||'<div class="empty">Area ini kosong. Posting untuk mencatat opname nol.</div>'}</div>`;}
  const acc=S.acc.length?sum(S.acc,x=>x)/S.acc.length:null;
  return`<div class="bar"><span class="muted small">Pilih area untuk dihitung. Selisih diposting sebagai koreksi stok dan tercatat di riwayat.</span><span class="sp"></span>${acc!=null?`<span class="tag g">Akurasi rata-rata ${nf(acc,1)}%</span>`:''}</div>
  <div class="tiles">${st.zones.filter(z=>ZT[z.type].multi).map(z=>{const lc=S.lastCount[z.id],age=lc?Math.floor((Date.now()-lc)/DAY):null,n=zoneBins(z).filter(b=>BB[b]).length;
    return`<div class="tile"><div class="row"><b style="font:600 17px var(--display);letter-spacing:.06em">${esc(z.code)} · ${esc(z.name)}</b>${age==null||age>30?'<span class="tag w">Jatuh tempo</span>':''}</div><span class="small muted">${n} bin terisi · terakhir ${lc?dfmt(lc)+' ('+age+' hari lalu)':'belum pernah'}</span>
    ${meter(age==null?1:clamp(age/30,0,1),age==null||age>30?'w':'g')}<div class="row"><button class="btn sm pri" data-a="cntStart" data-id="${z.id}">Mulai opname</button><button class="btn sm" data-a="selZone" data-id="${z.id}" data-go="1">Lihat di denah</button></div></div>`;}).join('')}</div>`;};

function tasks(st){const o=[],tb=stg(st,'terima');
  for(const p of S.pos)if(p.site===st.id&&p.status==='tiba')o.push({k:'rcv'+p.id,type:'Terima',c:'k1',t:`${p.no} · ${p.sup}`,m:`${sum(p.lines,l=>l.qty-l.recv)} unit di dock`,a:'receive',id:p.id});
  for(const r of tb?BB[tb]||[]:[]){const sg=suggest(r.sku,r.qty,st,{},1)[0];o.push({k:'put'+r.id,type:'Simpan',c:'k4',t:`${nf(r.qty)} × ${SK[r.sku].name}`,m:`${binCode(tb)} → ${sg?binCode(sg.bin):'belum ada bin'}`,a:'putOne',id:r.id});}
  for(const s of S.sos)if(s.site===st.id){const n=sum(s.lines,l=>l.alloc.filter(a=>!a.done).length);
    if(s.status==='alokasi'&&n)o.push({k:'pick'+s.id,type:'Pick',c:'k5',t:`${s.no} · ${s.cust}`,m:`${n} titik ambil · tenggat ${tfmt(s.due)}`,a:'pick',id:s.id});
    if(s.status==='pick')o.push({k:'pack'+s.id,type:'Kemas',c:'k3',t:`${s.no} · ${s.cust}`,m:'Sudah di area pengiriman',a:'pack',id:s.id});
    if(s.status==='kemas')o.push({k:'ship'+s.id,type:'Muat',c:'k2',t:`${s.no} · ${s.cust}`,m:`${s.koli||1} koli · tenggat ${tfmt(s.due)}`,a:'ship',id:s.id});}
  for(const z of st.zones)if(ZT[z.type].multi&&(!S.lastCount[z.id]||Date.now()-S.lastCount[z.id]>30*DAY))o.push({k:'cnt'+z.id,type:'Opname',c:'k7',t:`${z.code} · ${z.name}`,m:'Lebih dari 30 hari sejak hitung terakhir',a:'cntStart',id:z.id});
  return o;}
BODY.tugas=()=>{const ts=tasks(site()),by=op=>ts.filter(t=>(S.assign[t.k]||'')===op),mx=Math.max(1,...OPS.map(o=>by(o).length));
  const card=t=>`<div class="card"><div class="hd1"><span class="tag" style="border-color:var(--${t.c});color:var(--${t.c})">${t.type}</span></div><span>${esc(t.t)}</span><span class="small muted">${esc(t.m)}</span>
    <div class="row"><select class="inp" style="padding:3px 6px;font-size:12.5px" data-assign="${t.k}" aria-label="Petugas"><option value="">Belum ditugaskan</option>${OPS.map(o=>`<option${S.assign[t.k]===o?' selected':''}>${o}</option>`).join('')}</select><button class="btn sm pri" data-a="${t.a}" data-id="${t.id}">Kerjakan</button></div></div>`;
  return`<div class="bar"><span class="muted small">Tugas diturunkan langsung dari dokumen dan stok, jadi selalu sinkron. Tugaskan ke petugas, lalu kerjakan.</span><span class="sp"></span><button class="btn" data-a="autoAssign">Bagi rata otomatis</button></div>
  <section class="panel" style="margin-bottom:14px"><div class="ph"><h2>Beban kerja</h2><span class="muted small">${ts.length} tugas terbuka</span></div><div class="pb">${OPS.map(o=>`<div class="hbar"><span>${o}</span><span class="num">${by(o).length}</span>${meter(by(o).length/mx,by(o).length>=mx&&mx>3?'w':'')}</div>`).join('')}</div></section>
  <div class="board">${lane('Belum ditugaskan',by('').length,by('').map(card).join(''))}${OPS.map(o=>lane(o,by(o).length,by(o).map(card).join(''))).join('')}</div>`;};

BODY.dock=()=>{const st=site(),d0=new Date();d0.setMinutes(0,0,0);const t0=d0.getTime()-4*HR,span=16*HR,pos=x=>(x-t0)/span*100,isToday=x=>{const t=new Date(x).getTime();return t>=t0-HR&&t<t0+span;};
  const ins=S.pos.filter(p=>p.site===st.id&&p.status!=='selesai'&&isToday(p.eta)).map(p=>({k:'po'+p.id,d:p,no:p.no,who:p.sup,a:new Date(p.eta).getTime(),b:new Date(p.eta).getTime()+HR})),
    outs=S.sos.filter(s=>s.site===st.id&&s.status!=='kirim'&&isToday(s.due)).map(s=>({k:'so'+s.id,d:s,no:s.no,who:s.cust,a:new Date(s.due).getTime()-HR,b:new Date(s.due).getTime(),out:1}));
  const rows=(items,n,lbl)=>{let h='';for(let i=0;i<n;i++){const on=items.filter(x=>x.d.dock===i);h+=`<div class="trow"><span>${lbl} ${i+1}</span><div class="trk">${on.map(x=>{const clash=on.some(y=>y!==x&&x.a<y.b&&y.a<x.b),l=clamp(pos(x.a),0,100),r=clamp(pos(x.b),0,100);
      return`<button class="tb${x.out?' out':''}${clash?' clash':''}" data-a="go" data-id="${x.out?'keluar':'masuk'}" style="left:${l}%;width:${Math.max(1.5,r-l)}%" title="${x.no} · ${esc(x.who)}${clash?' · bentrok jadwal':''}">${x.no}</button>`;}).join('')}</div></div>`;}return h;};
  const un=[...ins,...outs].filter(x=>x.d.dock==null),sel=x=>`<select class="inp" style="padding:3px 6px;font-size:12.5px" data-dock="${x.k}" aria-label="Pintu dock"><option value="">Pilih pintu</option>${Array.from({length:st.doors[x.out?1:0]},(_,i)=>`<option value="${i}">${x.out?'Keluar':'Masuk'} ${i+1}</option>`).join('')}</select>`;
  let ticks='';for(let h=0;h<=16;h+=2)ticks+=`<span style="left:${h/16*100}%">${tfmt(t0+h*HR)}</span>`;const np=pos(Date.now());
  return`<div class="bar"><span class="muted small">Jendela 16 jam: 4 jam lalu sampai 12 jam ke depan. Truk masuk menempati pintu 1 jam sejak tiba, truk keluar 1 jam sebelum tenggat. Bentrok ditandai merah.</span></div>
  <div class="cols"><section class="panel"><div class="ph"><h2>Pintu dock · ${esc(st.name)}</h2></div><div class="tlscroll"><div class="tl"><div class="ticks">${ticks}</div>${np>=0&&np<=100?`<div class="now" style="left:calc(120px + (100% - 120px) * ${np/100})"></div>`:''}${rows(ins,st.doors[0],'Masuk')}<div style="height:8px"></div>${rows(outs,st.doors[1],'Keluar')}</div></div></section>
  <aside class="rail"><section class="panel"><div class="ph"><h2>Belum dijadwalkan</h2><span class="muted small">${un.length}</span></div><div class="pb">${un.map(x=>`<div class="item"><div class="row"><b class="num">${x.no}</b><span class="tag">${x.out?'Keluar':'Masuk'}</span><span class="muted small">${tfmt(x.out?x.b:x.a)}</span></div><span class="small">${esc(x.who)}</span>${sel(x)}</div>`).join('')||'<span class="muted">Semua truk hari ini sudah punya pintu.</span>'}</div></section></aside></div>`;};

BODY.jaringan=()=>{const n=S.sites.length,Wd=Math.max(640,n*250),xs=S.xfers.filter(x=>x.status==='transit'),cx=i=>Wd/n*(i+.5);
  let h=`<svg class="net" viewBox="0 0 ${Wd} 250" style="min-width:${Math.min(Wd,640)}px">`;
  xs.forEach((x,j)=>{const a=S.sites.findIndex(s=>s.id===x.from),b=S.sites.findIndex(s=>s.id===x.to);if(a<0||b<0)return;const y=40-j*8;h+=`<path class="ed" d="M${cx(a)} 70 C${cx(a)} ${y},${cx(b)} ${y},${cx(b)} 70"/><text class="sub" x="${(cx(a)+cx(b))/2}" y="${y+22}" text-anchor="middle">${x.no} · ${nf(sum(x.items,i=>i.qty))} unit</text>`;});
  S.sites.forEach((s,i)=>{const recs=S.stock.filter(r=>inSite(r,s)),cap=sum(s.zones,z=>single(z)?0:zoneBins(z).length*z.cap),occ=cap?sum(s.zones,z=>single(z)?0:sum(zoneBins(z),used))/cap:0,x=cx(i)-105;
    h+=`<g data-a="setSite" data-id="${s.id}" style="cursor:pointer"><rect class="nd${s.id===S.cur?' cur':''}" x="${x}" y="70" width="210" height="160" rx="8"/><text x="${x+14}" y="96">${esc(s.name)}</text><text class="sub" x="${x+14}" y="113">${esc(s.city)} · ${s.zones.length} area</text>
    <text class="sub" x="${x+14}" y="140">Nilai stok</text><text x="${x+196}" y="140" text-anchor="end">${rp(sum(recs,r=>r.qty*SK[r.sku].price))}</text><text class="sub" x="${x+14}" y="160">SKU · unit</text><text x="${x+196}" y="160" text-anchor="end">${new Set(recs.map(r=>r.sku)).size} · ${nf(sum(recs,r=>r.qty))}</text>
    <text class="sub" x="${x+14}" y="180">Order · PO terbuka</text><text x="${x+196}" y="180" text-anchor="end">${S.sos.filter(o=>o.site===s.id&&o.status!=='kirim').length} · ${S.pos.filter(p=>p.site===s.id&&p.status!=='selesai').length}</text>
    <rect x="${x+14}" y="198" width="182" height="8" rx="2" style="fill:var(--line)"/><rect x="${x+14}" y="198" width="${182*clamp(occ,0,1)}" height="8" rx="2" style="fill:var(--k1)"/><text class="sub" x="${x+14}" y="222">Okupansi ${nf(occ*100)}%</text></g>`;});
  const imb=S.skus.map(k=>{const q=S.sites.map(s=>onHand(k.id,s));return{k,q,lo:Math.min(...q),hi:Math.max(...q)};}).filter(x=>x.lo<x.k.min*.5&&x.hi>x.k.max*.6).slice(0,8);
  return`<div class="bar"><span class="muted small">Klik gudang untuk berpindah. Garis putus-putus adalah kiriman antar gudang yang sedang di jalan.</span><span class="sp"></span><button class="btn pri" data-a="xfer">+ Kirim antar gudang</button></div>
  <section class="panel" style="margin-bottom:14px"><div style="overflow-x:auto;padding:10px">${h}</svg></div></section>
  <div class="charts"><section class="panel"><div class="ph"><h2>Dalam perjalanan</h2></div><div class="pb">${xs.map(xferCard).join('')||'<span class="muted">Tidak ada kiriman berjalan.</span>'}</div></section>
  <section class="panel"><div class="ph"><h2>Saran penyeimbangan</h2></div><div class="pb">${imb.map(x=>{const hi=x.q.indexOf(x.hi),lo=x.q.indexOf(x.lo);return`<div class="item"><h4>${esc(x.k.name)}</h4><span class="small muted">${esc(S.sites[hi].name)} punya <span class="num">${nf(x.hi)}</span>, ${esc(S.sites[lo].name)} tinggal <span class="num">${nf(x.lo)}</span> (min ${x.k.min})</span><div class="row"><button class="btn sm" data-a="xfer" data-id="${x.k.id}" data-from="${S.sites[hi].id}" data-to="${S.sites[lo].id}">Siapkan transfer</button></div></div>`;}).join('')||'<span class="muted">Stok antar gudang seimbang.</span>'}</div></section></div>`;};

BODY.analitik=()=>{const st=site(),mv=S.moves.filter(m=>mvInSite(m,st)),d0=new Date();d0.setHours(0,0,0,0);
  const days=[];for(let i=13;i>=0;i--){const a=d0.getTime()-i*DAY;days.push({a,i:0,o:0});}
  for(const m of mv){const d=days.find(d=>m.t>=d.a&&m.t<d.a+DAY);if(!d)continue;if(m.type==='terima')d.i+=m.qty;else if(m.type==='kirim')d.o+=m.qty;}
  const mx=Math.max(1,...days.map(d=>Math.max(d.i,d.o))),recs=S.stock.filter(r=>inSite(r,st));
  const cat=CATS.map(c=>[c,sum(recs,r=>SK[r.sku].cat===c?r.qty*SK[r.sku].price:0)]),cm=Math.max(1,...cat.map(c=>c[1]));
  const lim=Date.now()-30*DAY,out={};for(const m of mv)if(m.type==='kirim'&&m.t>=lim)out[m.sku]=(out[m.sku]||0)+m.qty;const top=Object.entries(out).filter(([id])=>SK[id]).sort((a,b)=>b[1]-a[1]).slice(0,8),tm=top.length?top[0][1]:1;
  const age=[['0–30 hari',0,30],['31–60 hari',31,60],['61–90 hari',61,90],['> 90 hari',91,1e9]].map(([l,a,b])=>[l,sum(recs,r=>{const d=(Date.now()-r.recv)/DAY;return d>=a&&d<b+1?r.qty*SK[r.sku].price:0;})]),am=Math.max(1,...age.map(a=>a[1]));
  const zs=st.zones.filter(z=>ZT[z.type].multi).map(z=>[z,zoneFill(z)]),ab=abcMap(),abc=['A','B','C'].map(c=>[c,S.skus.filter(k=>ab[k.id]===c).length]);
  const shipped=S.sos.filter(s=>s.site===st.id&&s.status==='kirim'),fr=shipped.length?shipped.filter(s=>!s.short).length/shipped.length*100:null,dead=recs.filter(r=>!out[r.sku]&&(Date.now()-r.recv)/DAY>60);
  const P2=(t,b,x='')=>`<section class="panel"><div class="ph"><h2>${t}</h2>${x}</div><div class="pb">${b}</div></section>`,hb=(l,v,f,c='')=>`<div class="hbar"><span>${l}</span><span class="num">${v}</span>${meter(f,c)}</div>`;
  return`<div class="stats">${[['Unit masuk 14 hari',nf(sum(days,d=>d.i))],['Unit keluar 14 hari',nf(sum(days,d=>d.o))],['Order terkirim lengkap',fr==null?'—':nf(fr)+'%'],['Akurasi opname',S.acc.length?nf(sum(S.acc,x=>x)/S.acc.length,1)+'%':'—'],['Stok mati > 60 hari',rp(sum(dead,r=>r.qty*SK[r.sku].price)),dead.length?'w':'']].map(([l,v,c])=>`<div class="stat ${c||''}"><span class="eyebrow">${l}</span><b>${v}</b></div>`).join('')}</div>
  <div class="charts">${P2('Arus barang 14 hari',`<div class="vbars">${days.map(d=>`<div class="d" title="${dfmt(d.a)} · masuk ${nf(d.i)} · keluar ${nf(d.o)}"><i style="height:${d.i/mx*100}%;background:var(--k1)"></i><i style="height:${d.o/mx*100}%;background:var(--k2)"></i></div>`).join('')}</div><div class="vax">${days.map((d,i)=>`<span>${i%2?'':new Date(d.a).getDate()}</span>`).join('')}</div><div class="row small muted"><span><i class="dot" style="background:var(--k1)"></i>Masuk</span><span><i class="dot" style="background:var(--k2)"></i>Keluar</span><span>puncak ${nf(mx)} unit/hari</span></div>`)}
  ${P2('Nilai stok per kategori',cat.map(([c,v])=>hb(`<i class="dot" style="background:${catCol(c)}"></i>${c}`,rp(v),v/cm)).join(''))}
  ${P2('Paling laku 30 hari',top.map(([id,q])=>hb(esc(SK[id].name),nf(q)+' '+SK[id].uom,q/tm,'y')).join('')||'<span class="muted">Belum ada pengiriman.</span>')}
  ${P2('Umur stok (nilai)',age.map(([l,v],i)=>hb(l,rp(v),v/am,i===3?'w':'')).join(''))}
  ${P2('Okupansi per area',zs.map(([z,f])=>hb(esc(z.code+' · '+z.name),nf(f*100)+'%',f,f>.9?'w':'')).join(''))}
  ${P2('Kelas ABC',abc.map(([c,n])=>hb(`Kelas ${c}`,n+' SKU',n/S.skus.length,c==='A'?'y':'')).join('')+'<span class="small muted">A = barang yang menyumbang 80% nilai keluar 30 hari terakhir. Simpan dekat area kemas.</span>')}</div>
  <section class="panel" style="margin-top:14px"><div class="ph"><h2>Riwayat gerakan</h2><span class="muted small">60 terakhir</span></div><div class="pb"><div class="stream">${mv.slice(-60).reverse().map(mvHTML).join('')}</div></div></section>`;};

/* ================= lembar form ================= */
let SUB=null;
function sheet(title,html,onSubmit,label){$('#sheetT').textContent=title;$('#sheetF').innerHTML=html+`<div class="sfoot"><button type="button" class="btn" data-a="closeSheet">${onSubmit?'Batal':'Tutup'}</button>${onSubmit?`<button class="btn pri" type="submit">${label||'Simpan'}</button>`:''}</div>`;SUB=onSubmit;$('#sheet').hidden=false;$('#sheetF').scrollTop=0;}
const closeSheet=()=>{$('#sheet').hidden=true;SUB=null;};
const fld=(l,html)=>`<label class="fld"><span>${l}</span>${html}</label>`;
const skuOpts=sel=>S.skus.slice().sort((a,b)=>a.name.localeCompare(b.name)).map(k=>`<option value="${k.id}"${k.id==sel?' selected':''}>${esc(k.name)} · ${k.code}</option>`).join('');
const lrow=(sel,q=10)=>`<div class="lrow"><select class="inp" name="sku" aria-label="Barang">${skuOpts(sel)}</select><input class="inp num" name="qty" type="number" min="1" value="${q}" aria-label="Jumlah"><button type="button" class="btn sm" data-a="rmRow" aria-label="Hapus baris">×</button></div>`;
const linesEd=rows=>`<span class="eyebrow">Barang</span><div id="lrows" style="display:flex;flex-direction:column;gap:6px">${rows}</div><div><button type="button" class="btn sm" data-a="addRow">+ Tambah baris</button></div>`;
function readLines(fd){const m={},ids=fd.getAll('sku'),qs=fd.getAll('qty');ids.forEach((id,i)=>{const q=Math.floor(+qs[i]);if(q>0)m[id]=(m[id]||0)+q;});return Object.entries(m).map(([sku,qty])=>({sku:+sku,qty}));}
function poSheet(lines,sup){sheet('Pesanan pembelian baru',`<div class="frow">${fld('Pemasok',`<input class="inp" name="sup" list="supl" required value="${esc(sup||'')}"><datalist id="supl">${[...new Set(S.skus.map(k=>k.sup))].map(s=>`<option value="${esc(s)}">`).join('')}</datalist>`)}${fld('Perkiraan tiba',`<input class="inp" type="datetime-local" name="eta" required value="${iso(Date.now()+DAY)}">`)}</div>${linesEd((lines||[{sku:S.skus[0].id,qty:50}]).map(l=>lrow(l.sku,l.qty)).join(''))}`,
  fd=>{const ls=readLines(fd);if(!ls.length)return toast('Isi minimal satu barang',1),false;mkPO(fd.get('sup'),site().id,fd.get('eta'),ls);commit('PO dibuat');},'Buat PO');}
function soSheet(){sheet('Order penjualan baru',`<div class="frow">${fld('Pelanggan',`<input class="inp" name="cust" list="cusl" required><datalist id="cusl">${[...new Set(S.sos.map(s=>s.cust))].map(s=>`<option value="${esc(s)}">`).join('')}</datalist>`)}${fld('Tenggat kirim',`<input class="inp" type="datetime-local" name="due" required value="${iso(Date.now()+6*HR)}">`)}</div>${linesEd(lrow(S.skus[0].id,5))}`,
  fd=>{const ls=readLines(fd);if(!ls.length)return toast('Isi minimal satu barang',1),false;mkSO(fd.get('cust'),site().id,fd.get('due'),ls);commit('Order dibuat. Alokasikan stok untuk mulai pick.');},'Buat order');}
function receiveSheet(po){const st=S.sites.find(s=>s.id===po.site);if(!stg(st,'terima'))return toast('Tambahkan area bertipe Penerimaan di denah dulu',1);
  sheet(`Terima ${po.no}`,`<span class="muted small">${esc(po.sup)}. Isi jumlah yang benar-benar datang; sisanya tetap terbuka di PO.</span>${po.lines.map((l,i)=>{const k=SK[l.sku],rem=l.qty-l.recv;if(rem<=0)return'';
    return`<div class="item"><h4>${esc(k.name)}</h4><span class="code">dipesan ${l.qty} · sudah diterima ${l.recv} ${k.uom}</span><div class="frow">${fld('Diterima sekarang',`<input class="inp num" type="number" min="0" name="q${i}" value="${rem}">`)}${k.lot?fld('Lot',`<input class="inp num" name="lot${i}" value="L${String(new Date().getFullYear()).slice(2)}${pad(new Date().getMonth()+1)}${pad(new Date().getDate())}">`)+fld('Kedaluwarsa',`<input class="inp" type="date" name="exp${i}" value="${iso(Date.now()+240*DAY).slice(0,10)}">`):''}</div></div>`;}).join('')}`,
  fd=>{let n=0;po.lines.forEach((l,i)=>{const q=Math.floor(+fd.get('q'+i));if(q>0){receive(po,i,q,fd.get('lot'+i)||'',fd.get('exp'+i)||'');n+=q;}});if(!n)return toast('Tidak ada jumlah yang diisi',1),false;commit(`${n} unit masuk ke area penerimaan`);if(!L){putSheet();return false;}},'Terima');}
function putSheet(only){const st=site(),tb=stg(st,'terima'),recs=(tb?BB[tb]||[]:[]).filter(r=>!only||r.id===only);if(!recs.length)return closeSheet();const extra={},hl=new Set();
  const rows=recs.map(r=>{const k=SK[r.sku],sg=suggest(r.sku,r.qty,st,extra,6);if(sg[0]){extra[sg[0].bin]=(extra[sg[0].bin]||0)+r.qty*(k.vol||1);hl.add(sg[0].bin);}
    return`<div class="item"><h4>${nf(r.qty)} ${k.uom} · ${esc(k.name)}</h4><span class="code">${k.cat}${r.lot?' · lot '+esc(r.lot):''}</span>${fld('Simpan ke',`<select class="inp" name="b${r.id}">${sg.map(s=>`<option value="${s.bin}">${binCode(s.bin)} · ${s.why} · sisa ruang ${nf(s.free)}</option>`).join('')||'<option value="">Tidak ada bin yang muat</option>'}</select>`)}</div>`;}).join('');
  sheet('Simpan ke rak',`<span class="muted small">Saran lokasi: gabung dengan stok yang sama, lalu area sesuai kategori, lalu bin kosong. Bin kuning di denah adalah tujuan yang disarankan.</span>${mapSVG(st,{mini:true,hl,route:null})}${rows}`,
  fd=>{let n=0,fail=0;for(const r of recs){const b=fd.get('b'+r.id);if(!b){fail++;continue;}if(capOf(b)-used(b)<r.qty*(SK[r.sku].vol||1)){fail++;continue;}moveStock(r,r.qty,b,'putaway');index();n++;}
    HLX=null;commit(`${n} lot disimpan${fail?', '+fail+' tidak muat dan tetap di penerimaan':''}`);},'Konfirmasi simpan');}
function pickSheet(orders,wave){const steps=pickSteps(orders);if(!steps.length)return toast('Tidak ada yang perlu dipick',1);const st=S.sites.find(s=>s.id===orders[0].site);if(!stg(st,'kirim'))return toast('Tambahkan area bertipe Pengiriman di denah dulu',1);
  const route={site:st.id,start:steps.start,bins:steps.map(s=>s.a.bin)};
  sheet(wave?`Pick ${wave} · ${orders.length} order`:`Pick ${orders[0].no}`,`<span class="muted small">Urutan mengikuti rute terpendek dari area kemas. Lot dipilih FEFO.</span>${mapSVG(st,{mini:true,hl:new Set(route.bins),route})}
  ${steps.map((s,i)=>`<div class="item"><div class="row"><span class="tag y">${i+1}</span><b class="num">${binCode(s.a.bin)}</b><span>${nf(s.a.qty)} ${SK[s.ln.sku].uom}</span></div><h4>${esc(SK[s.ln.sku].name)}</h4><span class="code">${s.so.no}${s.a.lot?' · lot '+esc(s.a.lot):''}</span></div>`).join('')}`,
  ()=>{for(const s of steps)pickAlloc(s.so,s.a,s.ln);if(wave)for(const o of orders)o.wave=wave;ROUTE=null;commit(`${steps.length} titik selesai dipick ke area pengiriman`);},'Konfirmasi semua terambil');}
function skuSheet(k){const st=site(),isNew=!k;k=k||{name:'',code:'',cat:CATS[0],uom:'pcs',price:10000,vol:1,min:20,max:80,lot:false,sup:''};
  const recs=isNew?[]:S.stock.filter(r=>r.sku===k.id).sort((a,b)=>(a.exp||'9').localeCompare(b.exp||'9')),d0=new Date();d0.setHours(0,0,0,0);
  const days=[];for(let i=29;i>=0;i--)days.push({a:d0.getTime()-i*DAY,i:0,o:0});if(!isNew)for(const m of S.moves){if(m.sku!==k.id)continue;const d=days.find(d=>m.t>=d.a&&m.t<d.a+DAY);if(d){if(m.type==='terima')d.i+=m.qty;if(m.type==='kirim')d.o+=m.qty;}}
  const mx=Math.max(1,...days.map(d=>Math.max(d.i,d.o)));
  sheet(isNew?'Barang baru':k.name,`${isNew?'':`<div class="row"><b class="num" style="font-size:22px">${nf(onHand(k.id,st))} ${k.uom}</b>${stTag[stOf(k,st)]}<span class="muted small">di ${esc(st.name)}${L?' · jaringan '+nf(onHand(k.id)):''} · dipesan ${onOrder(k.id,st)}</span></div>
    <div class="row"><button type="button" class="btn sm" data-a="locate" data-id="${k.id}">Tunjukkan di denah</button><button type="button" class="btn sm" data-a="poFor" data-id="${k.id}">Buat PO</button><button type="button" class="btn sm" data-a="xfer" data-id="${k.id}">Pindahkan</button></div>
    <span class="eyebrow">Masuk & keluar 30 hari</span><div class="vbars" style="height:70px">${days.map(d=>`<div class="d" title="${dfmt(d.a)} · masuk ${d.i} · keluar ${d.o}"><i style="height:${d.i/mx*100}%;background:var(--k1)"></i><i style="height:${d.o/mx*100}%;background:var(--k2)"></i></div>`).join('')}</div>
    <span class="eyebrow">Lokasi & lot</span>${recs.map(r=>`<div class="item"><div class="row"><b class="num">${binCode(r.bin)}</b><span class="muted small">${esc(bz(r.bin).s.name)}</span><span class="num">${nf(r.qty)} ${k.uom}</span>${r.resv?`<span class="tag y">${r.resv} dialokasi</span>`:''}${expTag(r.exp)}</div>${r.lot?`<span class="code">lot ${esc(r.lot)} · masuk ${dfmt(r.recv)}</span>`:''}</div>`).join('')||'<span class="muted">Tidak ada stok.</span>'}<span class="eyebrow">Data induk</span>`}
  ${fld('Nama barang',`<input class="inp" name="name" required value="${esc(k.name)}">`)}<div class="frow">${fld('Kode',`<input class="inp num" name="code" required value="${esc(k.code)}">`)}${fld('Kategori',`<select class="inp" name="cat">${CATS.map(c=>`<option${c===k.cat?' selected':''}>${c}</option>`).join('')}</select>`)}${fld('Satuan',`<input class="inp" name="uom" required value="${esc(k.uom)}">`)}</div>
  <div class="frow">${fld('Stok minimum',`<input class="inp num" type="number" min="0" name="min" value="${k.min}">`)}${fld('Stok maksimum',`<input class="inp num" type="number" min="1" name="max" value="${k.max}">`)}${fld('Ruang per unit',`<input class="inp num" type="number" min="1" name="vol" value="${k.vol}">`)}</div>
  <div class="frow">${fld('Harga pokok (Rp)',`<input class="inp num" type="number" min="0" name="price" value="${k.price}">`)}${fld('Pemasok utama',`<input class="inp" name="sup" value="${esc(k.sup)}">`)}</div>
  <label class="row"><input type="checkbox" name="lot" ${k.lot?'checked':''}> Lacak lot dan tanggal kedaluwarsa (FEFO)</label>`,
  fd=>{const code=fd.get('code').trim().toUpperCase();if(S.skus.some(x=>x.code===code&&x.id!==k.id))return toast('Kode sudah dipakai barang lain',1),false;
    Object.assign(k,{name:fd.get('name').trim(),code,cat:fd.get('cat'),uom:fd.get('uom').trim(),min:+fd.get('min'),max:Math.max(+fd.get('max'),+fd.get('min')+1),vol:Math.max(1,+fd.get('vol')),price:+fd.get('price'),sup:fd.get('sup').trim(),lot:!!fd.get('lot')});
    if(isNew){k.id=S.seq++;S.skus.push(k);}ABC=null;commit(isNew?'Barang ditambahkan':'Data barang disimpan');},isNew?'Tambah barang':'Simpan perubahan');}
function xferSheet(skuId,from,to){const st=from?S.sites.find(s=>s.id===from):site(),id=+skuId||(S.stock.find(r=>inSite(r,st)&&r.qty-r.resv>0)||{}).sku;if(!id)return toast('Tidak ada stok bebas untuk dipindah',1);
  const recs=S.stock.filter(r=>r.sku===id&&inSite(r,st)&&r.qty-r.resv>0&&bz(r.bin).z.type!=='kirim'),dq=recs[0]?Math.min(10,recs[0].qty-recs[0].resv):1,sg=suggest(id,dq,st,{},14).filter(x=>!recs[0]||x.bin!==recs[0].bin).filter(x=>x.free>=dq*(SK[id].vol||1)).slice(0,12);
  sheet('Pindahkan stok',`${fld('Barang',`<select class="inp" name="sku" data-x="sku">${skuOpts(id)}</select>`)}<span class="eyebrow">Ambil dari · ${esc(st.name)}</span>${recs.map((r,i)=>`<label class="item" style="flex-direction:row;align-items:center;gap:10px"><input type="radio" name="rec" value="${r.id}" ${i?'':'checked'}><span><b class="num">${binCode(r.bin)}</b> · ${nf(r.qty-r.resv)} bebas${r.lot?' · lot '+esc(r.lot):''} ${expTag(r.exp)}</span></label>`).join('')||'<span class="muted">Barang ini tidak punya stok bebas di gudang ini.</span>'}
  <div class="frow">${fld('Jumlah',`<input class="inp num" type="number" min="1" name="qty" value="${dq}">`)}${fld('Tujuan',`<select class="inp" name="dst">${L?`<optgroup label="Gudang lain">${S.sites.filter(s=>s.id!==st.id).map(s=>`<option value="site:${s.id}"${s.id===to?' selected':''}>${esc(s.name)} (antar gudang)</option>`).join('')}</optgroup>`:''}<optgroup label="Bin di gudang ini">${sg.map(s=>`<option value="${s.bin}"${!to&&s===sg[0]?' selected':''}>${binCode(s.bin)} · ${s.why}</option>`).join('')}${st.zones.filter(z=>z.type==='karantina').map(z=>`<option value="${z.id}.0.0">${esc(z.code)} · karantina</option>`).join('')}</optgroup></select>`)}</div>`,
  fd=>{const r=S.stock.find(x=>x.id===+fd.get('rec')),q=Math.floor(+fd.get('qty')),dst=fd.get('dst');if(!r)return toast('Pilih sumber stok',1),false;if(!(q>0)||q>r.qty-r.resv)return toast(`Jumlah harus 1–${r.qty-r.resv}`,1),false;
    if(dst.startsWith('site:')){const x={id:S.seq++,no:'TR-'+(S.n.x++),from:st.id,to:dst.slice(5),status:'transit',t:Date.now(),items:[{sku:r.sku,qty:q,lot:r.lot,exp:r.exp}]};r.qty-=q;S.xfers.push(x);log('transfer',r.sku,q,r.bin,'',x.no);commit(`${x.no} berangkat ke ${sname(x.to)}`);}
    else{if(capOf(dst)-used(dst)<q*(SK[r.sku].vol||1))return toast(`${binCode(dst)} tidak muat`,1),false;moveStock(r,q,dst,'pindah');commit(`Dipindah ke ${binCode(dst)}`);}},'Pindahkan');}
function dataSheet(){sheet('Data & cadangan',`<span class="muted small">Sistem ini berjalan tanpa server. Semua data tersimpan di browser ini saja. Salin teks di bawah untuk mencadangkan atau memindahkan ke perangkat lain.</span>
  <textarea class="inp" id="dataTxt" aria-label="Data JSON" spellcheck="false">${esc(JSON.stringify(S))}</textarea><div class="row"><button type="button" class="btn" data-a="copyData">Salin</button><button type="button" class="btn" data-a="importData">Muat dari teks di atas</button><button type="button" class="btn danger" data-a="reset">Kembalikan data contoh</button></div>
  <span class="muted small">Tombol reset meminta konfirmasi kedua sebelum menghapus.</span>`);}

/* ================= aksi ================= */
const byId=(arr,id)=>arr.find(x=>x.id===+id);
let resetArm=0;
const ACT={
  closeSheet,go:d=>{location.hash=d.id;},
  lens:d=>{LENS=d.id;refresh();},
  edit:()=>{EDIT=!EDIT;TOOL='sel';PEND=null;if(!EDIT)SEL=null;refresh();},
  tool:d=>{TOOL=d.id;refresh();},
  zoom:d=>{const s=site();if(d.id==='fit')fitVB();else{const f=d.id==='in'?1/1.4:1.4,cx=VB[0]+VB[2]/2,cy=VB[1]+VB[3]/2,w=clamp(VB[2]*f,8,s.w+2),h=w*(s.h+2)/(s.w+2);VB=[cx-w/2,cy-h/2,w,h];}redrawMap();},
  unsel:()=>{SEL=null;refresh();},clearHL:()=>{HLX=null;ROUTE=null;refresh();},
  selZone:d=>{SEL={z:d.id};if(d.go||V!=='peta')location.hash='peta';refresh();},
  selBin:d=>{SEL={b:d.id};if(V!=='peta')location.hash='peta';else refresh();},
  setSite:d=>{S.cur=d.id;SEL=null;PEND=null;HLX=null;ROUTE=null;fitVB();saveSoon();chrome();refresh();},
  fcat:d=>{FILT.cat=d.id;refresh();},
  newSku:()=>skuSheet(),sku:d=>skuSheet(byId(S.skus,d.id)),
  locate:d=>{const k=byId(S.skus,d.id),st=site();HLX=new Set(S.stock.filter(r=>r.sku===k.id&&inSite(r,st)).map(r=>r.bin));HLX.label=k.name;ROUTE=null;closeSheet();location.hash='peta';refresh();},
  poFor:d=>{const k=byId(S.skus,d.id);poSheet([{sku:k.id,qty:Math.max(1,k.max-onHand(k.id,site())-onOrder(k.id,site()))}],k.sup);},
  reorder:()=>{const st=site(),low=S.skus.filter(k=>onHand(k.id,st)+onOrder(k.id,st)<k.min),g={};for(const k of low)(g[k.sup||'Tanpa pemasok']=g[k.sup||'Tanpa pemasok']||[]).push(k);
    if(!low.length)return toast('Tidak ada yang perlu dipesan. Stok dan pesanan berjalan sudah menutup minimum.');
    sheet('Saran pesan ulang',`<span class="muted small">Barang yang stok + pesanan berjalannya di bawah minimum. Jumlah saran mengisi sampai stok maksimum. Satu PO per pemasok.</span>${Object.entries(g).map(([s,ks])=>`<span class="eyebrow">${esc(s)}</span>${ks.map(k=>{const oh=onHand(k.id,st);return`<label class="item" style="flex-direction:row;gap:10px;align-items:center"><input type="checkbox" name="k" value="${k.id}" checked><span style="flex:1;min-width:0"><b>${esc(k.name)}</b><br><span class="small muted num">stok ${oh} · min ${k.min} · pesan ${k.max-oh-onOrder(k.id,st)} ${k.uom}</span></span></label>`;}).join('')}`).join('')}`,
    fd=>{const ids=fd.getAll('k').map(Number),g2={};for(const k of low)if(ids.includes(k.id))(g2[k.sup||'Tanpa pemasok']=g2[k.sup||'Tanpa pemasok']||[]).push({sku:k.id,qty:k.max-onHand(k.id,st)-onOrder(k.id,st)});
      const n=Object.keys(g2).length;if(!n)return toast('Pilih minimal satu barang',1),false;for(const s in g2)mkPO(s,st.id,iso(Date.now()+2*DAY),g2[s]);commit(`${n} PO dibuat`);location.hash='masuk';},'Buat PO');},
  newPO:()=>poSheet(),
  arrive:d=>{const p=byId(S.pos,d.id);p.status='tiba';p.arr=Date.now();commit(`${p.no} tiba di dock`);},
  delPO:d=>{const p=byId(S.pos,d.id);S.pos.splice(S.pos.indexOf(p),1);commit(`${p.no} dibatalkan`);},
  receive:d=>receiveSheet(byId(S.pos,d.id)),
  putAll:()=>{if(V!=='masuk'&&V!=='peta'&&V!=='tugas')location.hash='masuk';putSheet();},putOne:d=>putSheet(+d.id),
  retur:()=>{const st=site();if(!stg(st,'karantina'))return toast('Tambahkan area bertipe Karantina & retur di denah dulu',1);
    sheet('Retur pelanggan',`<span class="muted small">Barang retur masuk ke karantina dulu. Setelah diperiksa, pindahkan ke rak atau koreksi keluar.</span>${fld('Barang',`<select class="inp" name="sku">${skuOpts()}</select>`)}<div class="frow">${fld('Jumlah',`<input class="inp num" type="number" min="1" name="qty" value="1">`)}${fld('Alasan',`<select class="inp" name="why"><option>Rusak saat kirim</option><option>Salah barang</option><option>Mendekati kedaluwarsa</option><option>Pembatalan</option></select>`)}</div>${fld('Dari pelanggan',`<input class="inp" name="cust">`)}`,
    fd=>{const id=+fd.get('sku'),q=Math.floor(+fd.get('qty'));if(!(q>0))return false;const b=stg(st,'karantina');addStock(id,b,q,'RETUR','');log('retur',id,q,'',b,fd.get('cust'),fd.get('why'));commit('Retur dicatat di karantina');},'Catat retur');},
  newSO:()=>soSheet(),
  alloc:d=>{const s=byId(S.sos,d.id);allocate(s);commit(s.short?`${s.no} dialokasi, kurang ${s.short} unit`:`${s.no} dialokasi penuh`);},
  allocAll:()=>{const st=site(),ss=S.sos.filter(s=>s.site===st.id&&s.status==='baru').sort((a,b)=>a.due.localeCompare(b.due));for(const s of ss){allocate(s);index();}commit(`${ss.length} order dialokasi, tenggat terdekat lebih dulu`);},
  pick:d=>pickSheet([byId(S.sos,d.id)]),
  wave:()=>{const st=site(),ss=S.sos.filter(s=>s.site===st.id&&s.status==='alokasi');pickSheet(ss,'W-'+(S.n.w++));},
  routeSO:d=>{const s=byId(S.sos,d.id),steps=pickSteps([s]);ROUTE={site:s.site,start:steps.start,bins:steps.map(x=>x.a.bin),label:s.no};HLX=null;location.hash='peta';refresh();},
  pack:d=>{const s=byId(S.sos,d.id);sheet(`Kemas ${s.no}`,`<span class="muted small">${esc(s.cust)} · ${sum(s.lines,l=>sum(l.alloc,a=>a.qty))} unit dari ${s.lines.length} baris.</span><div class="frow">${fld('Jumlah koli',`<input class="inp num" type="number" min="1" name="koli" value="${Math.max(1,Math.ceil(sum(s.lines,l=>l.qty)/20))}">`)}${fld('Berat total (kg)',`<input class="inp num" type="number" min="0" step="0.1" name="kg" value="${nf(sum(s.lines,l=>l.qty)*.8,1).replace(',','.')}">`)}</div>`,
    fd=>{s.koli=+fd.get('koli');s.kg=+fd.get('kg');s.status='kemas';commit(`${s.no} dikemas, ${s.koli} koli`);},'Selesai kemas');},
  ship:d=>{const s=byId(S.sos,d.id);sheet(`Kirim ${s.no}`,`<span class="muted small">${esc(s.cust)} · tenggat ${dtf(s.due)}. Stok keluar dari area pengiriman saat dikonfirmasi.</span>${fld('Pengangkut',`<select class="inp" name="car">${CARRIERS.map(c=>`<option>${c}</option>`).join('')}</select>`)}${fld('Nomor resi / kendaraan',`<input class="inp num" name="resi">`)}`,
    fd=>{ship(s,fd.get('car'));s.resi=fd.get('resi');commit(`${s.no} terkirim`);},'Konfirmasi berangkat');},
  cancelSO:d=>{const s=byId(S.sos,d.id);cancelSO(s);commit(`${s.no} dibatalkan, alokasi dilepas`);},
  xfer:d=>xferSheet(d.id,d.from,d.to),
  xrecv:d=>{const x=byId(S.xfers,d.id),st=S.sites.find(s=>s.id===x.to),b=st&&stg(st,'terima');if(!b)return toast('Gudang tujuan belum punya area Penerimaan',1);for(const i of x.items){addStock(i.sku,b,i.qty,i.lot,i.exp);log('terima',i.sku,i.qty,'',b,x.no);}x.status='selesai';commit(`${x.no} diterima di ${st.name}`);},
  mvStart:d=>{const r=byId(S.stock,d.id);PEND={rec:r.id,qty:r.qty-r.resv};SEL=null;refresh();},mvCancel:()=>{PEND=null;refresh();},
  quar:d=>{const r=byId(S.stock,d.id),b=stg(bz(r.bin).s,'karantina');if(!b)return toast('Tambahkan area bertipe Karantina & retur di denah dulu',1);const q=moveStock(r,r.qty-r.resv,b,'pindah','karantina');SEL={b};commit(`${q} unit dipindah ke karantina`);},
  adjust:d=>{const r=byId(S.stock,d.id),k=SK[r.sku];sheet(`Koreksi ${binCode(r.bin)}`,`<span class="muted small">${esc(k.name)}${r.lot?' · lot '+esc(r.lot):''}. Sistem mencatat ${r.qty} ${k.uom}${r.resv?', '+r.resv+' di antaranya sudah dialokasi':''}.</span><div class="frow">${fld('Jumlah sebenarnya',`<input class="inp num" type="number" min="${r.resv}" name="qty" value="${r.qty}">`)}${fld('Alasan',`<select class="inp" name="why"><option>Rusak</option><option>Hilang</option><option>Kedaluwarsa, dimusnahkan</option><option>Salah catat</option><option>Ditemukan</option></select>`)}</div>`,
    fd=>{const q=Math.floor(+fd.get('qty'));if(!(q>=r.resv))return toast(`Minimal ${r.resv} karena sudah dialokasi ke order`,1),false;const diff=q-r.qty;if(!diff)return;log('sesuai',r.sku,diff,r.bin,'',fd.get('why'));r.qty=q;commit(`Stok dikoreksi ${diff>0?'+':''}${diff}`);},'Posting koreksi');},
  cntStart:d=>{const e=ZI[d.id];if(S.counts.some(c=>c.status==='buka'&&ZI[c.zone]&&ZI[c.zone].s.id===e.s.id))return toast('Selesaikan opname yang sedang berjalan dulu',1),location.hash='opname';
    S.counts.push({id:S.seq++,no:'OP-'+(S.n.c++),zone:d.id,t:Date.now(),status:'buka',lines:zoneBins(e.z).flatMap(b=>(BB[b]||[]).map(r=>({bin:b,sku:r.sku,lot:r.lot,sys:r.qty,cnt:null})))});saveSoon();if(V==='opname')refresh();else location.hash='opname';},
  cntFill:()=>{const c=curCount();for(const l of c.lines)if(l.cnt==null)l.cnt=l.sys;saveSoon();refresh();},
  cntCancel:()=>{const c=curCount();S.counts.splice(S.counts.indexOf(c),1);commit('Opname dibatalkan, stok tidak berubah');},
  cntPost:()=>{const c=curCount();let nd=0;for(const l of c.lines){const d=l.cnt-l.sys;if(!d)continue;nd++;const r=S.stock.find(x=>x.bin===l.bin&&x.sku===l.sku&&x.lot===l.lot);if(r){r.qty=Math.max(0,r.qty+d);r.resv=Math.min(r.resv,r.qty);}else if(d>0)addStock(l.sku,l.bin,d,l.lot,'');log('opname',l.sku,d,l.bin,'',c.no);}
    c.status='selesai';S.lastCount[c.zone]=Date.now();if(c.lines.length){S.acc.push((1-nd/c.lines.length)*100);if(S.acc.length>12)S.acc.shift();}commit(`${c.no} diposting: ${nd} selisih dari ${c.lines.length} baris`);},
  autoAssign:()=>{const ts=tasks(site());let i=0;for(const t of ts)if(!S.assign[t.k])S.assign[t.k]=OPS[i++%OPS.length];saveSoon();refresh();},
  delZone:d=>{const e=ZI[d.id];if(zoneHasStock(e.z))return toast('Area masih berisi stok. Pindahkan dulu isinya.',1);if(S.counts.some(c=>c.status==='buka'&&c.zone===d.id))return toast('Area sedang diopname',1);e.s.zones.splice(e.s.zones.indexOf(e.z),1);SEL=null;commit('Area dihapus');},
  addSite:()=>{const id='s'+S.seq++;S.sites.push({id,name:'Gudang baru',city:'',w:40,h:24,doors:[1,1],zones:[{id:'z'+S.seq++,type:'terima',code:'IN',name:'Penerimaan',x:1,y:1,w:8,h:8,cols:1,rows:1,cap:120,cat:''},{id:'z'+S.seq++,type:'kirim',code:'OUT',name:'Pengiriman',x:1,y:15,w:8,h:8,cols:1,rows:1,cap:120,cat:''}]});S.cur=id;SEL=null;fitVB();chrome();commit('Gudang baru dibuat. Gambar area raknya.');},
  delSite:()=>{const st=site();if(S.stock.some(r=>inSite(r,st))||S.pos.some(p=>p.site===st.id&&p.status!=='selesai')||S.sos.some(s=>s.site===st.id&&s.status!=='kirim')||S.xfers.some(x=>x.status==='transit'&&(x.to===st.id||x.from===st.id)))return toast('Gudang masih punya stok atau dokumen berjalan',1);
    S.sites.splice(S.sites.indexOf(st),1);S.cur=S.sites[0].id;SEL=null;fitVB();chrome();commit('Gudang dihapus');},
  addRow:()=>{$('#lrows').insertAdjacentHTML('beforeend',lrow(S.skus[0].id,10));},rmRow:(d,el)=>{if($('#lrows').children.length>1)el.closest('.lrow').remove();},
  data:()=>dataSheet(),
  copyData:()=>{const t=$('#dataTxt');t.select();(navigator.clipboard?navigator.clipboard.writeText(t.value):Promise.reject()).then(()=>toast('Data disalin')).catch(()=>toast('Teks sudah dipilih. Tekan Ctrl/Cmd + C untuk menyalin.'));},
  importData:()=>{try{const o=JSON.parse($('#dataTxt').value);if(!o||o.v!==1||o.profile!==P||!Array.isArray(o.sites)||!o.sites.length)throw 0;S=o;ABC=null;SEL=null;fitVB();closeSheet();chrome();commit('Data dimuat');}catch(e){toast('Teks bukan cadangan yang valid untuk versi ini',1);}},
  reset:(d,el)=>{if(Date.now()-resetArm>4000){resetArm=Date.now();el.textContent='Tekan sekali lagi untuk menghapus semua';return;}seed();ABC=null;SEL=null;PEND=null;HLX=null;ROUTE=null;fitVB();closeSheet();chrome();commit('Data contoh dikembalikan');}
};
const curCount=()=>S.counts.find(c=>c.status==='buka'&&ZI[c.zone]&&ZI[c.zone].s.id===site().id);
document.addEventListener('click',e=>{const el=e.target.closest('[data-a]');if(el&&ACT[el.dataset.a]){if(el.tagName==='A')e.preventDefault();ACT[el.dataset.a](el.dataset,el);}else if(e.target.id==='sheet')closeSheet();});
document.addEventListener('keydown',e=>{if(e.key==='Escape'&&!$('#sheet').hidden)closeSheet();});
document.addEventListener('submit',e=>{if(e.target.id!=='sheetF')return;e.preventDefault();if(SUB&&SUB(new FormData(e.target),e.target)!==false)closeSheet();});
document.addEventListener('input',e=>{if(e.target.id==='q'){Q=e.target.value;HLX=null;if(V==='peta'||V==='stok')refresh();}});
document.addEventListener('change',e=>{const el=e.target,d=el.dataset;
  if(el.id==='siteSel')return ACT.setSite({id:el.value});
  if(d.f){FILT[d.f]=el.value;return refresh();}
  if(d.pq!=null&&PEND){const r=S.stock.find(x=>x.id===PEND.rec);PEND.qty=clamp(Math.floor(+el.value)||1,1,r.qty-r.resv);return;}
  if(d.x==='sku')return xferSheet(el.value);
  if(d.assign){if(el.value)S.assign[d.assign]=el.value;else delete S.assign[d.assign];saveSoon();return refresh();}
  if(d.dock){const doc=d.dock.startsWith('po')?byId(S.pos,d.dock.slice(2)):byId(S.sos,d.dock.slice(2));if(el.value==='')delete doc.dock;else doc.dock=+el.value;return commit('Pintu dock dijadwalkan');}
  if(d.cnt!=null){const c=curCount(),l=c.lines[+d.cnt];l.cnt=el.value===''?null:Math.max(0,Math.floor(+el.value));saveSoon();return refresh();}
  if(d.sp){const st=site();if(d.sp==='w'||d.sp==='h'){const v=clamp(Math.round(+el.value)||0,d.sp==='w'?12:10,d.sp==='w'?160:100),need=Math.max(...st.zones.map(z=>d.sp==='w'?z.x+z.w:z.y+z.h),0);
      if(v<need)return toast(`Tidak bisa lebih kecil dari ${need} m: masih ada area di sana`,1),refresh();st[d.sp]=v;fitVB();}else st[d.sp]=el.value.trim()||st[d.sp];chrome();return commit();}
  if(d.zp&&SEL&&SEL.z){const z=ZI[SEL.z].z,st=ZI[SEL.z].s,k=d.zp;let v=el.value;
    if(k==='name')z.name=v.trim()||z.name;
    else if(k==='code'){v=v.trim().toUpperCase();if(!v||st.zones.some(o=>o!==z&&o.code===v))return toast('Kode harus unik di gudang ini',1),refresh();z.code=v;}
    else if(k==='type'){if(zoneHasStock(z))return toast('Kosongkan area dulu sebelum mengganti tipenya',1),refresh();z.type=v;if(!ZT[v].multi){z.cols=z.rows=1;}else{z.cols=Math.max(1,Math.floor(z.w/2));z.rows=Math.max(1,Math.floor((z.h-1.5)/2.5));}}
    else if(k==='cols'||k==='rows'){v=clamp(Math.round(+v)||1,1,k==='cols'?40:12);const bad=zoneBins(z).some(b=>{const[,r,c]=b.split('.');return BB[b]&&(k==='cols'?+c>=v:+r>=v);});if(bad)return toast('Ada stok di bin yang akan hilang. Pindahkan dulu.',1),refresh();z[k]=v;}
    else if(k==='cap')z.cap=Math.max(1,Math.round(+v)||1);
    else if(k==='cat')z.cat=v;
    return commit();}});
addEventListener('hashchange',routeTo);

/* ================= kerangka ================= */
function chrome(){$('#app').innerHTML=`<header class="top"><div class="brand"><h1>Nadi <span>Gudang</span> ${L?'Enterprise':'UKM'}</h1><small>${esc(S.company)} · ${L?S.sites.length+' gudang':esc(site().name)+', '+esc(site().city)} · ${S.skus.length} barang · data contoh, tersimpan di browser ini</small></div>
  ${L?`<select class="inp" id="siteSel" aria-label="Gudang aktif">${S.sites.map(s=>`<option value="${s.id}"${s.id===S.cur?' selected':''}>${esc(s.name)}</option>`).join('')}</select>`:''}
  <input class="inp" id="q" type="search" placeholder="Cari barang, kode, lot, atau bin…" aria-label="Cari" autocomplete="off" value="${esc(Q)}" style="width:250px"><button class="btn" data-a="data">Data</button></header>
  <nav class="nav" aria-label="Modul">${VIEWS.map(([k,l])=>`<a href="#${k}" data-nav="${k}">${l}<b hidden></b></a>`).join('')}</nav><div id="vbody"></div>`;chromeBadges();navActive();}
function chromeBadges(){const st=site(),set=(k,n)=>{const b=document.querySelector(`[data-nav="${k}"] b`);if(b){b.hidden=!n;b.textContent=n;}},tb=stg(st,'terima');
  set('peta',alerts(st).filter(a=>a.sev==='crit').length);set('masuk',S.pos.filter(p=>p.site===st.id&&p.status==='tiba').length+(tb&&BB[tb]?1:0));set('keluar',S.sos.filter(s=>s.site===st.id&&s.status!=='kirim'&&new Date(s.due)<Date.now()).length);
  if(L){set('tugas',tasks(st).filter(t=>!S.assign[t.k]).length);set('jaringan',S.xfers.filter(x=>x.status==='transit').length);}}
const navActive=()=>document.querySelectorAll('[data-nav]').forEach(a=>a.dataset.nav===V?a.setAttribute('aria-current','page'):a.removeAttribute('aria-current'));
function refresh(){ABC=null;$('#vbody').innerHTML=BODY[V]();}
function routeTo(){const h=location.hash.slice(1);V=VIEWS.some(v=>v[0]===h)?h:'peta';if(V!=='peta'){EDIT=false;PEND=null;}navActive();refresh();scrollTo(0,0);}

S=load();if(!S)seed();else index();
document.body.insertAdjacentHTML('beforeend','<div id="sheet" hidden><div class="sheetbox" role="dialog" aria-modal="true" aria-labelledby="sheetT"><div class="ph"><h2 id="sheetT"></h2><button class="btn sm" data-a="closeSheet">Tutup</button></div><form id="sheetF"></form></div></div><div id="toasts" aria-live="polite"></div>');
fitVB();chrome();routeTo();
})();
