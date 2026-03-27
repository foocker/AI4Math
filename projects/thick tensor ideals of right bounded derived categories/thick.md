reference: https://msp.org/ant/2017/11-7/ant-v11-n7-p07-p.pdf or https://arxiv.org/abs/1611.02826 

The main goal of this task is to investigate Remark 7.22. other is background. We do not know if it holds for $d \geqslant 3$. just this question.



Example 7.21. Let $x \in R$ be a nonzerodivisor. For integers $a, b, c \geqslant 0$, define a complex

$$
X(a, b, c)=\bigoplus_{i \geqslant 0}\left(R / f_i\right)[i]=\left(\cdots \stackrel{0}{\rightarrow} R / f_2 \xrightarrow{0} R / f_1 \xrightarrow{0} R / f_0 \rightarrow 0\right),
$$

where $f_i=x^{a i^2+b i+c} \in R$. Then it holds that thick ${ }^{\otimes}\{X(a, b, c) \mid a, b, c \geqslant 0\}=$ thick $^{\otimes}\{X(1,0,0)\}$.

Proof. It is obvious that the left-hand side contains the right-hand side. In view of Lemma 7.20, the opposite inclusion will follow if we show that $X(1,0,0), X(0,1,0)$, $X(0,0,1)$ are in thick ${ }^{\otimes}\{X(1,0,0)\}$, whose first containment is evident. The complex $X(1,0,0)$ has the direct summand $(R / x)[1]$, so the module $R / x$ belongs to thick ${ }^{\otimes}\{X(1,0,0)\}$. We have $X(0,0,1)=R / x \otimes_R^L(\cdots \xrightarrow{0} R \xrightarrow[2 i+1]{0} R \rightarrow 0)$, which is in thick ${ }^{\otimes}\{X(1,0,0)\}$. The exact sequences $0 \rightarrow R / x^{i^2} \xrightarrow{x^{2 i+1}} R / x^{(i+1)^2} \rightarrow R / x^{2 i+1} \rightarrow 0$ and $0 \rightarrow R / x^{2 i+1} \xrightarrow{x} R / x^{2 i+2} \rightarrow R / x \rightarrow 0$ with $i>0$ induce


exact sequences $0 \rightarrow X(1,0,0) \rightarrow X(1,0,0)[-1] \rightarrow X(0,2,1) \rightarrow 0$ and $0 \rightarrow X(0,2,1) \rightarrow X(0,2,2) \rightarrow X(0,0,1) \rightarrow 0$, which shows that thick ${ }^{\otimes}\{X(1,0,0)\}$ contains $X(0,2,1)=\left(\cdots \xrightarrow{0} R / x^5 \xrightarrow{0} R / x^3 \xrightarrow{0} R / x \rightarrow 0\right)$ and $X(0,2,2)=(\cdots)^0 R / x^6 \xrightarrow{0} R / x^4 \xrightarrow{0} R / x^2 \rightarrow 0$ ). Applying Corollary 7.3, we see that $X(0,1,0)$ belongs to thick ${ }^{\otimes}\{X(1,0,0)\}$.

Remark 7.22. One can consider a general statement of Example 7.21 by defining $f_i=x^{a_0 i^d+a_1 i^{d-1}+\cdots+a_d}$, so that it is nothing but the example for $d=2$. We do not know if it holds for $d \geqslant 3$.


Lemma 7.20. Let $x$ be a nonzerodivisor of $R$. Then the complex $\bigoplus_{i \geqslant 0}\left(R / x^{a_i+b_i}\right)[i]$ belongs to the thick closure of $\bigoplus_{i \geqslant 0}\left(R / x^{a_i}\right)[i]$ and $\bigoplus_{i \geqslant 0}\left(R / x^{b_i}\right)[i]$ for all integers $a_i, b_i \geqslant 0$. In particular, the complex $\bigoplus_{i \geqslant 0}\left(R / x^{c a_i}\right)[i]$ is in the thick closure of $\bigoplus_{i \geqslant 0}\left(R / x^{a_i}\right)[i]$ for all integers $c, a_i \geqslant 0$.
Proof. For each $i \geqslant 0$ there is an exact sequence $0 \rightarrow R / x^{a_i} \xrightarrow{x^{b_i}} R / x^{a_i+b_i} \rightarrow R / x^{b_i} \rightarrow 0$. From this we induce an exact sequence $0 \rightarrow \bigoplus_{i \geqslant 0}\left(R / x^{a_i}\right)[i] \rightarrow \bigoplus_{i \geqslant 0}\left(R / x^{a_i+b_i}\right)[i] \rightarrow \bigoplus_{i \geqslant 0}\left(R / x^{b_i}\right)[i] \rightarrow 0$. The first assertion follows from this.
The second assertion is shown by induction and the first assertion.

Example 7.21. Let $x \in R$ be a nonzerodivisor. For integers $a, b, c \geqslant 0$, define a complex

$$
X(a, b, c)=\bigoplus_{i \geqslant 0}\left(R / f_i\right)[i]=\left(\cdots \stackrel{0}{\rightarrow} R / f_2 \xrightarrow{0} R / f_1 \xrightarrow{0} R / f_0 \rightarrow 0\right),
$$

where $f_i=x^{a i^2+b i+c} \in R$. Then it holds that thick ${ }^{\otimes}\{X(a, b, c) \mid a, b, c \geqslant 0\}=$ thick $^{\otimes}\{X(1,0,0)\}$.


Proposition 7.2. Let $X=\bigoplus_{i \geqslant 0} X_i[i]=\left(\cdots \xrightarrow{0} X_3 \xrightarrow{0} X_2 \xrightarrow{0} X_1 \xrightarrow{0} X_0 \rightarrow 0\right)$ be a complex in $\mathrm{D}^{-}(R)$. Then for all integers $a_i \geqslant 0$, the thick $\otimes$-ideal closure thick ${ }^{\otimes} X$ in $\mathrm{D}^{-}(R)$ contains

$$
\bigoplus_{i \geqslant 0} X_i^{\oplus a_i}[2 i]=\left(\cdots \rightarrow X_3^{\oplus a_3} \rightarrow 0 \rightarrow X_2^{\oplus a_2} \rightarrow 0 \rightarrow X_1^{\oplus a_1} \rightarrow 0 \rightarrow X_0^{\oplus a_0} \rightarrow 0\right) .
$$


Proof. The complex $\bigoplus_{i \geqslant 0} X_i^{\oplus a_i}[2 i]=\bigoplus_{i \geqslant 0}\left(X_i \otimes_R^L R^{\oplus a_i}\right)[2 i]$ is a direct summand of $\bigoplus_{i, j \geqslant 0}\left(X_i \otimes_R^L R^{\oplus a_j}\right)[i+j]=\left(\bigoplus_{i \geqslant 0} X_i[i]\right) \otimes_R^L\left(\bigoplus_{j \geqslant 0} R^{\oplus a_j}[j]\right)=X \otimes_R^L Y$ in the category $\mathrm{D}^{-}(R)$, where $Y=\bigoplus_{j \geqslant 0} R^{\oplus a_j}[j]=\left(\cdots \xrightarrow{0} R^{\oplus a_2} \xrightarrow{0} R^{\oplus a_1} \xrightarrow{0} R^{\oplus a_0} \rightarrow 0\right)$ is a complex in $\mathrm{D}^{-}(R)$. Thus, the assertion follows.


Corollary 7.3. Let $X=\bigoplus_{i \geqslant 0} X_i[i]=\left(\cdots \xrightarrow{0} X_3 \xrightarrow{0} X_2 \xrightarrow{0} X_1 \xrightarrow{0} X_0 \rightarrow 0\right)$ be a complex in $\mathrm{D}^{-}(R)$. Then for any integers $a_i \geqslant 0$ the complex

$$
Y=\bigoplus_{i \geqslant 0} X_i^{\oplus a_i}[i]=\left(\cdots{ }^0 X_3^{\oplus a_3} \xrightarrow{0} X_2^{\oplus a_2} \xrightarrow{0} X_1^{\oplus a_1} \xrightarrow{0} X_0^{\oplus a_0} \rightarrow 0\right)
$$

is in thick $^{\otimes}\left\{X_{\text {even }}, X_{\text {odd }}\right\}$, where $X_{\text {even }}=\bigoplus_{i \geqslant 0} X_{2 i}[i]=\left(\cdots \xrightarrow{0} X_6 \xrightarrow{0} X_4 \xrightarrow{0} X_2 \xrightarrow{0}\right. \left.X_0 \rightarrow 0\right)$ and $X_{\text {odd }}=\bigoplus_{i \geqslant 0} X_{2 i+1}[i]=\left(\cdots \xrightarrow{0} X_7 \xrightarrow{0} X_5 \xrightarrow{0} X_3 \xrightarrow{0} X_1 \rightarrow 0\right)$.
Proof. The complex $Y$ is the direct sum of $A=\left(\cdots \rightarrow 0 \rightarrow X_4^{\oplus a_4} \rightarrow 0 \rightarrow X_2^{\oplus a_2} \rightarrow\right. \left.0 \rightarrow X_0^{\oplus a_0} \rightarrow 0\right)$ and $B=\left(\cdots \rightarrow X_5^{\oplus a_5} \rightarrow 0 \rightarrow X_3^{\oplus a_3} \rightarrow 0 \rightarrow X_1^{\oplus a_1} \rightarrow 0 \rightarrow 0\right)$. Proposition 7.2 shows that $A$ is in thick ${ }^{\otimes} X_{\text {even }}$ and $B$ is in thick ${ }^{\otimes} X_{\text {odd }}$. Therefore, $Y$ belongs to thick ${ }^{\otimes}\left\{X_{\text {even }}, X_{\text {odd }}\right\}$.

